-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_gs_energy_with_promise_computable
-- name    : UndecidableSpectralGap.usg_gs_energy_with_promise_computable
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T12:19:09.228044+00:00
-- url     : https://prove2.me/theorems/1ff1b86f-1e2d-409b-a088-a2573cd5506a
-- title:
--   Corollary 54 - ground state energy with promise (computable interactions)
-- statement:
--   Let $u$ be a partial recursive code. The claim is that there is a translationally invariant nearest-neighbour model on the two-dimensional square lattice $\Lambda(L)=\{1,\dots,L\}^2$ with open boundary conditions, with local Hilbert space dimension $d$ and Hermitian interactions of operator norm at most $1/2$ with algebraic entries, whose ground state energy decides the halting problem for $u$ under a promise — and whose interactions are **computable functions of the input**.
--
--   Writing $H^{\Lambda(L)}(n)$ for the Hamiltonian assembled from the on-site term $h_1(n)$ and the nearest-neighbour terms $h_{\mathrm{row}}(n), h_{\mathrm{col}}(n)$, the three families $n \mapsto h_1(n), h_{\mathrm{row}}(n), h_{\mathrm{col}}(n)$ are uniformly computable and there is a threshold $L_{\mathrm{bd}}(n)$ such that:
--
--   1. if $u$ halts on $n$, then $1 \le \lambda_0(H^{\Lambda(L)}(n))$ for all $L \ge L_{\mathrm{bd}}(n)$;
--
--   2. if $u$ does not halt on $n$, then there is $L_1$ with $\lambda_0(H^{\Lambda(L)}(n)) \le 0$ for all $L \ge L_1$.
--
--   So on all sufficiently large lattices the ground state energy is either at least $1$ or at most $0$, and which alternative occurs is equivalent to the halting of $u$ on $n$. Since the interactions are computable from $n$ while the threshold $L_{\mathrm{bd}}$ is not, an algorithm determining the ground state energy to within $1/2$ under this promise would decide the halting problem.
--
--   **Formalization Note.** This statement replaces `usg_gs_energy_with_promise` and its repair `usg_gs_energy_with_promise_threshold`. The former is proved, but only because it omits the computability requirement: without it the statement is satisfied by a one-dimensional model whose single on-site parameter is defined by a case distinction on the halting of $u$ on $n$. Computability of the interaction family, in the sense of the definition `usg_computable_family`, is what carries the undecidability content, and algebraicity of the entries does not imply it. The non-halting clause is also required only from some size on, in parallel with the halting clause, matching the companion statement `usg_diverging_gs_energy_computable`.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), doi:10.1017/fmp.2021.15, Section 6.1, p. 94, Corollary 54.

import Definitions.Def_usg_computable_family

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

/-- **Corollary 54 (undecidability of the ground state energy with promise),
computable form.**

This is the companion of `usg_diverging_gs_energy_computable`. The interactions are
required to be a uniformly computable family in the input `n`, and the non-halting clause
is required only from some size `L₁` on, in parallel with the halting clause.

Both corrections are needed. Without computability the statement is satisfied by a
one-dimensional model defined by a case distinction on the halting of `u` on `n`, and
carries no undecidability content; and the non-halting bound cannot be imposed at `L = 1`
in the companion proposition, where the lattice has no nearest-neighbour pair.

Under the promise, the ground state energy of all sufficiently large lattices is either at
least `1` or at most `0`, and which of the two occurs is equivalent to the halting of `u`
on `n`; since the interactions are computable from `n`, deciding the ground state energy to
within `1/2` under this promise would decide the halting problem. -/
theorem usg_gs_energy_with_promise_computable (u : Nat.Partrec.Code) :
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (Lbound : ℕ → ℕ),
      -- the interactions are computable functions of the input
      ComputableMatrixFamily h1 ∧ ComputableMatrixFamily hrow ∧
        ComputableMatrixFamily hcol ∧
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        opNorm (h1 n) ≤ 1 / 2 ∧ opNorm (hrow n) ≤ 1 / 2 ∧ opNorm (hcol n) ≤ 1 / 2 ∧
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j))) ∧
      ∀ n : ℕ,
        -- non-halting case: beyond some size the ground state energy is non-positive
        (¬ (u.eval n).Dom → ∃ L1 : ℕ, ∀ L ≥ L1,
          gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)) ≤ 0) ∧
        -- halting case: ground state energy at least 1 from the size `Lbound n` on
        ((u.eval n).Dom → ∀ L ≥ Lbound n,
          1 ≤ gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n))) := by
  sorry

end UndecidableSpectralGap
