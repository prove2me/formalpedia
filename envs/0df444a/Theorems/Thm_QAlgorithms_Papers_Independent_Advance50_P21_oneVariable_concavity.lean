-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_oneVariable_concavity
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.oneVariable_concavity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:58:41.665907+00:00
-- url     : https://prove2.me/theorems/c79623fc-7079-4e02-8d22-fed2b7540755
-- title:
--   Theorem 16: one-variable sufficient concavity criterion
-- statement:
--   Let $d\ge2$, $r=d-1$, $c\ge0$, and let $h:\mathbb R\to\mathbb R$ be twice differentiable and nondecreasing. For $0\le x\le1/d$, define
--   $$s_r(x)=-rx\log x-(1-rx)\log(1-rx),\qquad w_r(x)=rx(1-rx)(\log x-\log(1-rx))^2,$$
--   using the continuous value $w_r(0)=0$ and continuous zero-weight entropy terms. If
--   $$c\,h''(cs_r(x))w_r(x)\le h'(cs_r(x))\qquad(0\le x\le1/d),$$
--   then $\rho\mapsto h(cH(\rho))$ is concave on all normalized $d$-dimensional states; $H$ is von Neumann entropy in nats. This is a sufficient one-variable criterion, including pure and uniform endpoints.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 22, Theorem 16: one-variable sufficient concavity criterion

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

/-- PDF p.22, Theorem 16, (6.48): sufficient one-variable criterion.
Printed quotients are read as c*h''(c*s)*w <= h'(c*s), as in (6.17), including w=0
at pure and uniform endpoints. No global differentiability of g^{-1} is asserted. -/
theorem oneVariable_concavity {d : ℕ} (hd : 2 ≤ d) (h : ℝ → ℝ)
    (hh : Differentiable ℝ h) (hhderiv : Differentiable ℝ (deriv h))
    (hmono : Monotone h) (c : ℝ) (hc : 0 ≤ c)
    (hcriterion : ∀ x ∈ Set.Icc (0 : ℝ) (1 / (d : ℝ)),
      c * deriv (deriv h) (c * peakEntropy d x) * peakVariance d x ≤
        deriv h (c * peakEntropy d x)) :
    StateConcave (fun rho : Mat d => h (c * entropy rho)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
