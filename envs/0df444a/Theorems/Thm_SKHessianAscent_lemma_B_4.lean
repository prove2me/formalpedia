-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_B_4
-- name    : SKHessianAscent.lemma_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-23T01:22:51.089562+00:00
-- url     : https://prove2.me/theorems/76f2ceb8-db8d-4613-a4a8-f244ef9af29a
-- title:
--   Lemma B.4 — Nishimori identity $\mathbf E[\tanh^3(Y^*)]=\mathbf E[\tanh^4(Y^*)]$ for the replica-symmetric cavity field
-- statement:
--   Let $0<\beta<1$, fix $t\ge0$ and let $h\sim N(0,1)$. Denote $Y^*=\beta^2m^*+t+\sqrt{\beta^2q^*+t}\,h$, where $(m^*,q^*)\in[0,1)^2$ solve the fixed-point equations in [DLSS26a, Theorem 5.1]. Then
--   $$\mathbf E_h\big[\tanh^3(Y^*)\big]=\mathbf E_h\big[\tanh^4(Y^*)\big].$$
--
--   **Formalization Note** The paper's statement names the Gaussian both $z$ and $h$, and does not restrict $\beta$; its proof uses $m^*=q^*$, which it derives for $0<\beta<1$, so $0<\beta<1$ is assumed. The solution is taken in $[0,1)^2$, where the paper asserts it is unique.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Appendix B, Lemma B.4, p. 49

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Localization
import Definitions.Def_SKHessianAscent_Cavity

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_B_4 (β t m q : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (ht : 0 ≤ t)
    (hm0 : 0 ≤ m) (hm1 : m < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (hfp : IsCavityFP β t m q) :
    cavityMean β t m q (fun y => Real.tanh y ^ 3) =
      cavityMean β t m q (fun y => Real.tanh y ^ 4) := by sorry

end SKHessianAscent
