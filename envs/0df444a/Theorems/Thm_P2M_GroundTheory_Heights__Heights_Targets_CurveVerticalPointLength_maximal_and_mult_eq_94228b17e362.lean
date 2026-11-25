-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointLength_maximal_and_mult_eq_94228b17e362
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointLength_maximal_and_mult_eq_94228b17e362
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:12:10.736568+00:00
-- url     : https://prove2.me/theorems/cc865930-cfc0-4d69-bd4a-d4f7dc660281
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Length maximal and mult eq 94228b17e362: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Length maximal and mult eq 94
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Length maximal and mult eq 94228b17e362 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Length maximal and mult eq 94228b17e362 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointLength.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointLength.lean#L15-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointLengthSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtPosOfMemDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointLength

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointLength_maximal_and_mult_eq_94228b17e362 (hCh : CurveVertPointChart.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ}
    (hP : IsArithVar (mCoordIdeal y) 1) (hs : IsMultiHomog s d) (hsP : s ∉ mCoordIdeal y)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
        locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointLength».«maximal_and_mult_eq» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointLength_maximal_and_mult_eq_94228b17e362
