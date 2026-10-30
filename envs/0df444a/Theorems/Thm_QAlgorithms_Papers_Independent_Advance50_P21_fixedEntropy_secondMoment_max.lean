-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_fixedEntropy_secondMoment_max
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.fixedEntropy_secondMoment_max
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:57:39.342738+00:00
-- url     : https://prove2.me/theorems/a18aa1e1-56c5-4e22-8533-5827e334b355
-- title:
--   Lemma 15: attained maximal logarithmic second moment at fixed entropy
-- statement:
--   Let $d\ge1$ and $H_0\in[0,\log d]$. For a probability vector $q$, let $H(q)=-\sum_iq_i\log q_i$ and $L(q)=\sum_iq_i(\log q_i)^2$, with continuous zero-weight values. There exists $x\in[0,1/d]$ such that, writing $r=d-1$ and $y=1-rx$, the vector $q_*=(x,\ldots,x,y)$ has $x\le y$ and $H(q_*)=H_0$, and
--   $$\max_{q:\,H(q)=H_0}L(q)=L(q_*)=rx(1-rx)\bigl(\log x-\log(1-rx)\bigr)^2+H_0^2.$$
--   The maximum is over all normalized nonnegative $d$-coordinate distributions and is attained. The variance term has value zero at $x=0$. This reduces the fixed-entropy maximization to a one-variable family, including the uniform endpoint.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 20, Lemma 15: attained maximal logarithmic second moment at fixed entropy

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

/-- PDF p.20, Lemma 15, (6.31)–(6.32), with endpoint repair justified pp.21–22.
Printed x<y is changed to x<=y: H0=ln d has the uniform maximizer x=y=1/d.
The maximum is attained, and the x=0 value uses the continuous variance extension. -/
theorem fixedEntropy_secondMoment_max {d : ℕ} (hd : 0 < d) (H0 : ℝ)
    (hH0 : H0 ∈ Set.Icc (0 : ℝ) (Real.log (d : ℝ))) :
    ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) (1 / (d : ℝ)) ∧
      x ≤ 1 - (d - 1 : ℕ) * x ∧
      oneHeavy d x ∈ simplex d ∧ simplexShannonNats (oneHeavy d x) = H0 ∧
      IsGreatest {v : ℝ | ∃ q ∈ simplex d, simplexShannonNats q = H0 ∧ v = logSecondMoment q}
        (logSecondMoment (oneHeavy d x)) ∧
      logSecondMoment (oneHeavy d x) = peakVariance d x + H0 ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
