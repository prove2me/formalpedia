-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_fractional_linear_perspective_convex
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.fractional_linear_perspective_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:28:00.425325+00:00
-- url     : https://prove2.me/theorems/188d2396-2865-4dec-9300-5c18c1105738
-- title:
--   Convexity under the fractional-linear perspective
-- statement:
--   Let $f:(1,+\infty)\to\mathbb R$ be convex. Define $\widetilde f:(0,1)\to\mathbb R$ by
--
--   $$
--   \widetilde f(u)=(1-u)f\!\left(\frac1{1-u}\right).
--   $$
--
--   Then $\widetilde f$ is convex on $(0,1)$. The input to $f$ is always greater than one, and $u=1$ is excluded. This is the perspective transformation used for the order variable in (4.29)–(4.31).
--
--   **Formalization Note** A total real function is constrained only on $(1,+\infty)$, so its other values are immaterial.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 19, Lemma 13, corrected domain

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P43

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Divergence relativeD petzD sandwichedD)

open QAlgorithms.Papers.Independent.Information100.P71
  (SupportIncluded supportPower AdaptiveTest adaptiveInput adaptiveAccept adaptiveBeta channelPower)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)
-- Exactly the trace-preparation map of PDF pp.5--6, on every operator.

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

/-- Lemma 13, arXiv:1408.3373v3, PDF pp.19--20.
SOURCE CORRECTION: printed f:(0,1)->R is undefined at 1/(1-u)>1.
Use convexity on (1,infinity), the order domain of F in (4.29)--(4.31).
ConvexOn of a total real function only uses its restriction to that domain. -/
theorem fractional_linear_perspective_convex
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ioi 1) f) :
    ConvexOn ℝ (Set.Ioo 0 1) (fun u => (1-u) * f (1/(1-u))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
