-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_nonconvexity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.nonconvexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:11:24.959491+00:00
-- url     : https://prove2.me/theorems/7d8b2063-df04-44d9-a877-77d985ae01bf
-- title:
--   The measure E_W is not convex
-- statement:
--   There exist nonzero finite local dimensions, normalized bipartite states $\rho,\sigma$ on the same product space, and a real parameter $0<p<1$ for which
--
--   $$E_W\bigl(p\rho+(1-p)\sigma\bigr)>pE_W(\rho)+(1-p)E_W(\sigma).$$
--
--   Here $E_W$ is the base-two logarithm of SDP (7). This existential violation of convexity is compatible with the monotonicity on average established in Theorem 3.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 3, Unnumbered result following Theorem 3: nonconvexity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Unnumbered nonconvexity assertion following Theorem 3, PDF p.3.
The violating pair and mixing parameter exist; no violation is assumed. -/
theorem nonconvexity :
    ∃ a b : ℕ, ∃ rho sigma : Matrix (Fin (a+1) × Fin (b+1)) (Fin (a+1) × Fin (b+1)) ℂ,
    IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
    p * entanglementW rho + (1-p) * entanglementW sigma <
      entanglementW ((p : ℂ) • rho + ((1-p : ℝ) : ℂ) • sigma) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
