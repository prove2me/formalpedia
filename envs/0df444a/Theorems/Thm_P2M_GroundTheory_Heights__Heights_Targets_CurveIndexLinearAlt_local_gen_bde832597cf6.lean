-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_local_gen_bde832597cf6
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_local_gen_bde832597cf6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:29.4248+00:00
-- url     : https://prove2.me/theorems/25cc4489-2b7e-52dc-a99c-28dfd3be0537
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt local gen bde832597cf6: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt local gen bde832597cf6
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt local gen bde832597cf6 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt local gen bde832597cf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L183-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L183-L217

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_local_gen_bde832597cf6 {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {m : Ideal (curveRing y)}
    (hm : m.IsPrime) {c' : ∀ k, ι k} (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0)
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c' p.1⟩) = α) (a : K → ℤ) :
    (∃ b : curveRing y, b ∉ m ∧ (b : Ω) * gen y c a c' ∈ secIdeal y c a) ∧
      ∀ z ∈ secIdeal y c a, ∃ b e : curveRing y, b ∉ m ∧ (b : Ω) * z = e * gen y c a c' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«local_gen» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_local_gen_bde832597cf6
