-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RankFracDegree_isFractionRing_of_closure_00df87cf7f7b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RankFracDegree_isFractionRing_of_closure_00df87cf7f7b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:58.389616+00:00
-- url     : https://prove2.me/theorems/163177b2-ee7e-492e-8957-334bab08a64c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Rank Frac Degree is Fraction Ring of closure 00df87cf7f7b: P2 M Ground Theory Heights  Heights Inter Rank Frac Degree is Fraction Ring of closure 00df87cf7f7b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Rank Frac Degree is Fraction Ring of closure 00df87cf7f7b construction uses the P2 M Ground Theory Heights  Heights Inter Rank Frac Degree is Fraction Ring of closure 00df87cf7f7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRankFracDegree.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRankFracDegree.lean#L9-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRankFracDegree
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

theorem P2M_GroundTheory_Heights__Heights_Inter_RankFracDegree_isFractionRing_of_closure_00df87cf7f7b {F Ω A : Type} [Field F] [Field Ω] [Algebra F Ω] [CommRing A]
    (K : IntermediateField F Ω) (f : A →+* Ω) (hf : Function.Injective f) (hK : ∀ a, f a ∈ K)
    (hcl : K.toSubfield ≤ Subfield.closure (Set.range f)) :
    let _ := (f.codRestrict K hK).toAlgebra
    IsFractionRing A K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RankFracDegree».«isFractionRing_of_closure» := P2M_GroundTheory_Heights__Heights_Inter_RankFracDegree_isFractionRing_of_closure_00df87cf7f7b
