-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_IntersectionEqChowHeight_hyps_inhabited_99b35b7292bc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_IntersectionEqChowHeight_hyps_inhabited_99b35b7292bc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:35.873454+00:00
-- url     : https://prove2.me/theorems/8ecaa86c-1a41-409b-b15f-0a70c7ee6c99
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Intersection Eq Chow Height hyps inhabited 99b35b7292bc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Intersection Eq Chow Height hyps inhabited 99b35b7292bc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Intersection Eq Chow Height hyps inhabited 99b35b7292bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L316-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L316-L320

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_IntersectionEqChowHeight_hyps_inhabited_99b35b7292bc :
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧
      IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1
        (map (Rat.castHom ℂ) (detForm ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ArithBezout».«IntersectionEqChowHeight».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_IntersectionEqChowHeight_hyps_inhabited_99b35b7292bc
