-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_threshold_upper_and_positive_liminf
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.threshold_upper_and_positive_liminf
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:19:33.77453+00:00
-- url     : https://prove2.me/theorems/961dcb28-2f60-4a12-9ca1-b2687dffa671
-- title:
--   Corollary III.3: upper branch and strictly positive lower liminf
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $\rho\in\mathcal D(H)$ be a normalized density operator. For each positive integer $n$, let $M_n\subseteq\mathcal D(H^{\otimes n})$ be closed and convex. Assume that one fixed full-rank state $\sigma$ has $\sigma^{\otimes n}\in M_n$ for every positive $n$, that every single-copy partial trace preserves the family, that tensor products map $M_n\times M_m$ into $M_{n+m}$, and that conjugation by every copy permutation preserves $M_n$. Define $E_{M_n}(\xi)=\inf_{\omega\in M_n}D_2(\xi\Vert\omega)$, using base-two relative entropy with value $+\infty$ on failed support inclusion, and define $E_M^\infty(\rho)=\inf_{n\ge1}E_{M_n}(\rho^{\otimes n})/n$.
--
--   Define $f_n(y)=\inf_{\omega\in M_n}\operatorname{Tr}(\rho^{\otimes n}-2^{ny}\omega)_+$. Then
--   $$
--   y>E_M^\infty(\rho)\ \Longrightarrow\ f_n(y)\to0,\qquad
--   y<E_M^\infty(\rho)\ \Longrightarrow\ \liminf_{n\to\infty}f_n(y)>0.
--   $$
--
--   The first printed threshold uses E_R; the proof Eq.(49) and the arbitrary-family context specify E_M. The lower branch states positive liminf, rather than convergence to one.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 10, Corollary III.3: upper branch and strictly positive lower liminf

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

/-- PDF pp.10--11 Corollary III.3 Eqs.(47),(48). SOURCE CORRECTION:
printed E_R^infinity in the upper branch is E_M^infinity, as its arbitrary-family
proof Eq.(49) states. The lower conclusion is only positive liminf. -/
theorem threshold_upper_and_positive_liminf {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (hM : stateSetAxioms M)
    (rho : Mat I) (hrho : IsDensityMatrix rho) :
    (∀ y : ℝ, (regularizedSetEntropy M rho : EReal) < (y : EReal) →
      Tendsto (thresholdProfile M rho y) atTop (𝓝 0)) ∧
    (∀ y : ℝ, (y : EReal) < (regularizedSetEntropy M rho : EReal) →
      0 < liminf (thresholdProfile M rho y) atTop) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
