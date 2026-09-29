-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_diverging_gs_energy_computable
-- name    : UndecidableSpectralGap.usg_diverging_gs_energy_computable
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T12:18:56.635358+00:00
-- url     : https://prove2.me/theorems/c8d7dc16-602b-4a84-86e9-e8b17c9b802c
-- title:
--   Proposition 53 - diverging ground state energy (computable interactions)
-- statement:
--   Let $u$ be a partial recursive code and let $\beta > 0$ be rational, as small as desired. The claim is that one can construct a translationally invariant nearest-neighbour model on the two-dimensional square lattice $\Lambda(L)=\{1,\dots,L\}^2$ with open boundary conditions whose ground state energy separates the halting from the non-halting instances of $u$, with interactions that are **computable functions of the input**.
--
--   There are a local Hilbert space dimension $d$ and, for every input $n$, an on-site term $h_1(n)$ and nearest-neighbour interactions $h_{\mathrm{row}}(n), h_{\mathrm{col}}(n)$, Hermitian, of operator norm at most $1/2$ and with algebraic matrix entries, such that the three families are uniformly computable in $n$, together with strictly positive reals $\delta_1(n), \delta_2(n)$, such that for
--
--   $$
--   H^{\Lambda(L)}(n) \;=\; \sum_{\text{row edges}} h_{\mathrm{row}}(n) \;+\; \sum_{\text{column edges}} h_{\mathrm{col}}(n) \;+\; \sum_{\text{sites}} h_1(n)
--   $$
--
--   the following two alternatives hold.
--
--   1. If $u$ does not halt on $n$, the ground state energy diverges at least linearly in the linear size: there is $L_1$ with $\lambda_0(H^{\Lambda(L)}(n)) \le -L\beta/2$ for all $L \ge L_1$.
--
--   2. If $u$ halts on $n$, the ground state energy is bounded below quadratically from some size on: there is $L_0$ with $L^2\delta_2(n) - L\delta_1(n) \le \lambda_0(H^{\Lambda(L)}(n))$ for all $L \ge L_0$.
--
--   In the first case the energy density $\lambda_0/L^2$ tends to $0$; in the second it is bounded below by $\delta_2(n) > 0$. The functions $\delta_1,\delta_2$ and the thresholds $L_0, L_1$ are not computable from $n$, whereas the interactions are — this asymmetry is the whole content of the proposition, and it is the point at which the halting information becomes a bulk thermodynamic quantity.
--
--   **Formalization Note.** This statement replaces the earlier formalisation `usg_diverging_gs_energy` of the same proposition, which is disproved, and its repair `usg_diverging_gs_energy_threshold`. Two changes are made. The non-halting bound is required only from some size $L_1$ on: demanded at every $L > 0$ it is false for $\beta > 1$, because $\Lambda(1)$ carries a single site and no nearest-neighbour pair, so $H^{\Lambda(1)}$ is the on-site term $h_1$ up to a relabelling of the basis and $\lVert h_1\rVert \le 1/2$ forces $\lambda_0(H^{\Lambda(1)}) \ge -1/2$. And the interaction family is required to be uniformly computable in $n$, in the sense of the definition `usg_computable_family`; without that hypothesis the statement is satisfied by a one-dimensional model defined by a case distinction on the halting of $u$ on $n$, and carries no undecidability content. Algebraicity of the entries does not replace it: it constrains each matrix separately and says nothing about the dependence on $n$.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), doi:10.1017/fmp.2021.15, Section 6.1, p. 93, Proposition 53 (Diverging g.s. energy).

import Definitions.Def_usg_computable_family

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

/-- **Proposition 53 (diverging ground state energy), computable form.**

Two corrections to the earlier formalisation `usg_diverging_gs_energy` are made here.

First, the non-halting bound `λ₀(H^Λ(L)) ≤ -Lβ/2` is required only from some size `L₁`
on, in parallel with the halting clause: demanding it at *every* size `L > 0` is
impossible as soon as `β > 1`, because `Λ(1)` has a single site and no nearest-neighbour
pair, so `H^Λ(1)` is the on-site term `h₁` up to a relabelling of the basis and the
normalisation `‖h₁‖ ≤ 1/2` forces `λ₀(H^Λ(1)) ≥ -1/2`.

Second, and more importantly, the family of interactions is required to be **uniformly
computable** in the input `n`. Without that requirement the statement carries no
undecidability content: the interactions may be defined by a case distinction on the
halting of `u` on `n`, and two constant one-dimensional models then satisfy both clauses.
Algebraicity of the entries does not substitute for it, since it constrains each matrix
separately and says nothing about the dependence of the family on `n`.

The functions `δ₁, δ₂` and the thresholds `L₀, L₁` remain arbitrary; they are the
uncomputable data of the proposition. -/
theorem usg_diverging_gs_energy_computable (u : Nat.Partrec.Code) (β : ℚ) (hβ : 0 < β) :
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (δ₁ δ₂ : ℕ → ℝ),
      -- the interactions are computable functions of the input
      ComputableMatrixFamily h1 ∧ ComputableMatrixFamily hrow ∧
        ComputableMatrixFamily hcol ∧
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        -- operator norms at most `1/2`
        opNorm (h1 n) ≤ 1 / 2 ∧ opNorm (hrow n) ≤ 1 / 2 ∧ opNorm (hcol n) ≤ 1 / 2 ∧
        -- algebraic matrix entries
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j)) ∧
        -- the two strictly positive functions of the statement
        0 < δ₁ n ∧ 0 < δ₂ n) ∧
      ∀ n : ℕ,
        -- non-halting case: beyond some size the ground state energy is at most `-Lβ/2`
        (¬ (u.eval n).Dom → ∃ L1 : ℕ, ∀ L ≥ L1,
          gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)) ≤ -(L : ℝ) * (β : ℝ) / 2) ∧
        -- halting case: beyond some size the ground state energy is at least
        -- `L²δ₂(n) - Lδ₁(n)`
        ((u.eval n).Dom → ∃ L0 : ℕ, ∀ L ≥ L0,
          (L : ℝ) ^ 2 * δ₂ n - (L : ℝ) * δ₁ n
            ≤ gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n))) := by
  sorry

end UndecidableSpectralGap
