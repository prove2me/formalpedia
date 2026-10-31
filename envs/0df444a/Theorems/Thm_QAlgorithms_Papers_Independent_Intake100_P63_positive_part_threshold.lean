-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_positive_part_threshold
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.positive_part_threshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:18:26.083183+00:00
-- url     : https://prove2.me/theorems/d30ae413-dbfa-462e-ba5d-d29e04df8ff8
-- title:
--   Proposition III.1: generalized positive-part threshold
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $\rho\in\mathcal D(H)$ be a normalized density operator. For each positive integer $n$, let $M_n\subseteq\mathcal D(H^{\otimes n})$ be closed and convex. Assume that one fixed full-rank state $\sigma$ has $\sigma^{\otimes n}\in M_n$ for every positive $n$, that every single-copy partial trace preserves the family, that tensor products map $M_n\times M_m$ into $M_{n+m}$, and that conjugation by every copy permutation preserves $M_n$. Define $E_{M_n}(\xi)=\inf_{\omega\in M_n}D_2(\xi\Vert\omega)$, using base-two relative entropy with value $+\infty$ on failed support inclusion, and define $E_M^\infty(\rho)=\inf_{n\ge1}E_{M_n}(\rho^{\otimes n})/n$.
--
--   For real $y$, define $f_n(y)=\inf_{\omega\in M_n}\operatorname{Tr}(\rho^{\otimes n}-2^{ny}\omega)_+$, where the positive-part trace is the sum of positive eigenvalues. The infimum is attained for every positive $n$, and
--   $$
--   y>E_M^\infty(\rho)\ \Longrightarrow\ f_n(y)\to0,\qquad
--   y<E_M^\infty(\rho)\ \Longrightarrow\ f_n(y)\to1.
--   $$
--
--   These are two strict threshold implications; the boundary value is left unspecified.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 7, Proposition III.1: generalized positive-part threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7 Proposition III.1 Eq.(20): minimum attainment and the two STRICT
branches. No value at y=E_M^infinity is asserted. -/
theorem positive_part_threshold {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (hM : stateSetAxioms M)
    (rho : Mat I) (hrho : IsDensityMatrix rho) :
    (∀ n, 0 < n → ∀ y : ℝ, ∃ omega ∈ M n,
      thresholdProfile M rho y n =
        (positivePart (piKron n rho - (((2 : ℝ) ^ (y * n) : ℝ) : ℂ) • omega)).trace.re) ∧
    (∀ y : ℝ, (regularizedSetEntropy M rho : EReal) < (y : EReal) →
      Tendsto (thresholdProfile M rho y) atTop (𝓝 0)) ∧
    (∀ y : ℝ, (y : EReal) < (regularizedSetEntropy M rho : EReal) →
      Tendsto (thresholdProfile M rho y) atTop (𝓝 1)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
