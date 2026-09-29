-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_diverging_gs_energy
-- name    : UndecidableSpectralGap.usg_diverging_gs_energy
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-13T05:02:28.791732+00:00
-- url     : https://prove2.me/theorems/6a2b7442-b2bd-4d8c-84b7-93c311a0a537
-- title:
--   Proposition 53 - diverging ground state energy
-- statement:
--   Fix a universal machine and a rational $\beta>0$, which may be taken as small as desired. There are a fixed local Hilbert space dimension $d$, Hermitian interactions $h_1(n),h_{\mathrm{row}}(n),h_{\mathrm{col}}(n)$ with algebraic (hence computable) matrix entries and operator norm at most $\tfrac12$, and strictly positive functions $\delta_1(n),\delta_2(n)$, such that for every input $n$ exactly one of the following two alternatives holds for the associated family $\{H_u^{\Lambda(L)}(n)\}_L$ on the square lattice with open boundary conditions:
--
--   1. the machine does not halt on $n$, and then $\lambda_0(H_u^{\Lambda(L)}(n))\le-L\beta/2$ for every $L\ge1$;
--
--   2. the machine halts on $n$, and then there is a size $L_0$ with $\lambda_0(H_u^{\Lambda(L)}(n))\ge L^2\delta_2(n)-L\delta_1(n)$ for all $L\ge L_0$.
--
--   In the first case the ground state energy is negative but grows only linearly in $L$, so the energy **density** $\lambda_0/L^2$ tends to $0$; in the second it grows quadratically, so the density is bounded below by $\delta_2(n)>0$. The functions $\delta_1,\delta_2$ and the threshold $L_0$ are not computable from $n$. This is the point of the construction at which the halting information becomes a bulk thermodynamic quantity.
--
--   **Formalization note.** Machines are represented by partial recursive codes, and the halting of the machine on input $n$ is definedness of the evaluation at $n$.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 6.1, p. 93, Proposition 53 (Diverging g.s. energy).

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_diverging_gs_energy (u : Nat.Partrec.Code) (β : ℚ) (hβ : 0 < β) :
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (δ₁ δ₂ : ℕ → ℝ),
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
        -- non-halting case: the ground state energy is at most `-Lβ/2` for every size
        (¬ (u.eval n).Dom → ∀ L : ℕ, 0 < L →
          gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)) ≤ -(L : ℝ) * (β : ℝ) / 2) ∧
        -- halting case: beyond some size the ground state energy is at least `L²δ₂(n) - Lδ₁(n)`
        ((u.eval n).Dom → ∃ L0 : ℕ, ∀ L ≥ L0,
          (L : ℝ) ^ 2 * δ₂ n - (L : ℝ) * δ₁ n
            ≤ gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n))) := by
  sorry

end UndecidableSpectralGap
