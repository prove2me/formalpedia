-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_finite_universal_compression
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.finite_universal_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:46:20.130458+00:00
-- url     : https://prove2.me/theorems/f4918470-ae58-4a74-aa0f-336662c8a888
-- title:
--   Remark 25: finite universal compression construction
-- statement:
--   Let $D\ge1$ and $0<\varepsilon\le1$. There is a universal visible quantum-classical compression code whose quantum code space has exactly
--
--   $$S=\left\lceil(1-\varepsilon/2)D\right\rceil$$
--
--   dimensions and whose fixed classical message support has size $K$ satisfying
--
--   $$\log_2K\le\lceil\varepsilon^{-1}\rceil,\qquad
--   F\bigl(\psi,\mathcal D_{m(\psi)}(\xi(\psi))\bigr)\ge(1-\varepsilon)^2\quad\text{for every pure }\psi.$$
--
--   Alice's quantum codeword is a normalized pure state in the $S$-dimensional space, and each message decoder is CPTP and fixed independently of the target. The cost bound is the printed number of cbits, rather than its logarithm. Padding gives the stated exact code dimension, with an identity code when $S=D$.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 16, Remark 25: finite universal compression construction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Remark 25, PDF pp.16–17: the source's ceil(1/eps) CBITS bound, not its logarithm.
Pad the code to exactly ceil((1-eps/2)D); when that equals D, use the identity code. -/
theorem finite_universal_compression (D : ℕ) (hD : 0 < D)
    (eps : ℝ) (heps : 0 < eps) (hepsOne : eps ≤ 1) :
    ∃ P : VisibleCode D, P.S = ⌈(1 - eps / 2) * D⌉₊ ∧
      Real.logb 2 P.K ≤ (⌈eps⁻¹⌉₊ : ℝ) ∧
      ∀ psi : RSPVector (Fin D), (1 - eps) ^ 2 ≤
        (pureDensity psi.val * P.output psi).trace.re := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
