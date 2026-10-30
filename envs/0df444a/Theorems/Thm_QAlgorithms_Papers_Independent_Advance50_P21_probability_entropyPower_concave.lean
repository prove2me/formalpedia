-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_probability_entropyPower_concave
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.probability_entropyPower_concave
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:59:43.752793+00:00
-- url     : https://prove2.me/theorems/57709458-bd94-4389-9ada-21daa9d310b7
-- title:
--   Unnumbered probability-simplex entropy-power concavity (§6.1)
-- statement:
--   Let $d\ge2$ and $0\le c\le(\log d)^{-2}$. For any normalized nonnegative probability vectors $p,q$ on $d$ elements and any $a\in[0,1]$, writing $H(p)=-\sum_i p_i\log p_i$ with $0\log0=0$,
--   $$e^{cH(ap+(1-a)q)}\ge a e^{cH(p)}+(1-a)e^{cH(q)}.$$
--   Thus finite-simplex entropy power is concave in this range. This is the classical diagonal specialization of the qudit concavity result.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 23, Unnumbered probability-simplex entropy-power concavity (§6.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.23, end of Section 6.1: entropy-power concavity on the finite probability simplex. -/
theorem probability_entropyPower_concave {d : ℕ} (hd : 2 ≤ d)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / (Real.log (d : ℝ)) ^ 2) :
    ∀ p ∈ simplex d, ∀ q ∈ simplex d, ∀ a ∈ Set.Icc (0 : ℝ) 1,
      a * Real.exp (c * simplexShannonNats p) + (1 - a) * Real.exp (c * simplexShannonNats q) ≤
        Real.exp (c * simplexShannonNats (a • p + (1 - a) • q)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
