-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_toRingHom_apply_80ffa5b2f707
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_toRingHom_apply_80ffa5b2f707
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:14.937805+00:00
-- url     : https://prove2.me/theorems/d45ef24e-0ec4-47ad-b04d-1f2549f0b4a5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin to Ring Hom apply 80ffa5b2f707: P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin to Ring Hom apply 80ffa5b2f707
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin to Ring Hom apply 80ffa5b2f707 construction uses the P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin to Ring Hom apply 80ffa5b2f707 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFnDegAdjoin.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFnDegAdjoin.lean#L33-L35

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

theorem P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_toRingHom_apply_80ffa5b2f707 {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (a : A) :
    f.toRingHom a = f a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FnDegAdjoin».«toRingHom_apply» := P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_toRingHom_apply_80ffa5b2f707
