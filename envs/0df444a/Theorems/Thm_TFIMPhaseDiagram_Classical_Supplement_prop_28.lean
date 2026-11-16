-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_prop_28
-- name    : TFIMPhaseDiagram.Classical.Supplement.prop_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:06:26.385559+00:00
-- url     : https://prove2.me/theorems/d14172e8-fa8e-4bb1-b841-6e22dd94a2c4
-- title:
--   Proposition 28 — Exact rate minimum and quadratic LDP rate bound
-- statement:
--   Under the supercritical assumptions, let $I,J$ be the extended rate functions of Proposition 25 and let $m_\ast$ be the positive magnetization of Proposition 26. Then
--   $$\inf I=I(m_\ast1)=-\Phi_{b,\eta}(bm_\ast1).$$
--   The tilted average laws satisfy a norm-topology LDP at speed $n$, and every $x\in L^2(S)$ satisfies
--   $$
--   J(x)\ge\Phi_{b,\eta}(bm_\ast1)-\Phi_{b,\eta}(bx)\ge c\min_{s\in\{-1,1\}}\|x-sm_\ast1\|^2,
--   $$
--   with the same constant $c$ as Lemma 27. The equality identifies the actual infimum and its attainment, rather than only giving a lower bound.
--
--   Differences from the source:
--   - encoding: the real finite rate minimum and the constant c from Lemma 27 → an extended-real infimum identified with its attained real value, and functionalGap; reason: retains infinite off-domain rate values while fixing the common proof witness
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 16, Proposition 28

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement
attribute [local instance] Classical.propDecidable

/-- Proposition 28, p.16. The infimum remains extended-real until identified. -/
theorem prop_28 (b η : ℝ) (h : supercritical b η) :
    rateMinimum b η = unnormalizedRate b η (constL2 (magnetization b η)) ∧
    unnormalizedRate b η (constL2 (magnetization b η)) =
      ((-phi b η (constL2 (b * magnetization b η)) : ℝ) : EReal) ∧
    HasNormLDP (tiltedAverageLaw b η) (cwRate b η) ∧
    (∀ x : CircleL2,
      ((phi b η (constL2 (b * magnetization b η)) - phi b η (b • x) : ℝ) : EReal) ≤ cwRate b η x ∧
      functionalGap b η * phaseDistanceSq (magnetization b η) x ≤
        phi b η (constL2 (b * magnetization b η)) - phi b η (b • x)) := by sorry

end TFIMPhaseDiagram.Classical.Supplement
