-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_div_83e03c384ca6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_div_83e03c384ca6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:29.530797+00:00
-- url     : https://prove2.me/theorems/fefd57d3-c930-491a-8d8f-5aded27867df
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval scale div 83e03c384ca6: P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval scale div 83e03c384ca6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval scale div 83e03c384ca6 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval scale div 83e03c384ca6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean#L39-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_div_83e03c384ca6 (y : (Σ k, ι k) → Ω) {c : K → Ω} (hc : ∀ k, c k ≠ 0) {u w : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hw : IsMultiHomog w a) :
    aeval (fun p => y p * c p.1) u / aeval (fun p => y p * c p.1) w = aeval y u / aeval y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRankFrac».«aeval_scale_div» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_div_83e03c384ca6
