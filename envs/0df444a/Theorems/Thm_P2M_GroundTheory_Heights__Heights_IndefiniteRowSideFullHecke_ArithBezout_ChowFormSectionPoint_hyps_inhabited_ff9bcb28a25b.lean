-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowFormSectionPoint_hyps_inhabited_ff9bcb28a25b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowFormSectionPoint_hyps_inhabited_ff9bcb28a25b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:50.284505+00:00
-- url     : https://prove2.me/theorems/81518e0d-431c-4a30-ad68-468f54dd1cd6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Chow Form Section Point hyps inhabited ff9bcb28a25b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Chow Form Section Point hyps inhabited ff9bcb28a25b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Chow Form Section Point hyps inhabited ff9bcb28a25b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L413-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L413-L423

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowFormSectionPoint_hyps_inhabited_ff9bcb28a25b :
    IsArithVar (⊥ : Ideal (MRing (PBlk 1))) (0 + 1) ∧
      IsIntChowForm (⊥ : Ideal (MRing (PBlk 1))) 0 1 (X (0, 0)) ∧
        linForm (![1] : Fin 1 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 1))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ArithBezout».«ChowFormSectionPoint».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowFormSectionPoint_hyps_inhabited_ff9bcb28a25b
