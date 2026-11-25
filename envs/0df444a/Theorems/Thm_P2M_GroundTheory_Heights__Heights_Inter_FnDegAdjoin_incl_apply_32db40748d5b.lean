-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_incl_apply_32db40748d5b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_incl_apply_32db40748d5b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:36.83806+00:00
-- url     : https://prove2.me/theorems/72f9bab2-d6ea-4bbf-bcd5-db9c041cc77b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin incl apply 32db40748d5b: P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin incl apply 32db40748d5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin incl apply 32db40748d5b construction uses the P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin incl apply 32db40748d5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFnDegAdjoin.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFnDegAdjoin.lean#L29-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFnDegAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFnDegAdjoin
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {σ : Type}

theorem P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_incl_apply_32db40748d5b {S T : Subalgebra F Ω} (h : S ≤ T) (x : S) :
    ((Subalgebra.inclusion h).toRingHom x : Ω) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FnDegAdjoin».«incl_apply» := P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_incl_apply_32db40748d5b
