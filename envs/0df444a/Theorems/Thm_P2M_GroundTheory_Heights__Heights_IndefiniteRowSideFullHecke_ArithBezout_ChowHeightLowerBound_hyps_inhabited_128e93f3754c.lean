-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowHeightLowerBound_hyps_inhabited_128e93f3754c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowHeightLowerBound_hyps_inhabited_128e93f3754c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:19.466877+00:00
-- url     : https://prove2.me/theorems/9ce3d793-ccbd-4d50-b4b7-c39610d05a9f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Chow Height Lower Bound hyps inhabited 128e93f3754c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Chow Height Lower Bound hyps inhabited 128e93f3754c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Chow Height Lower Bound hyps inhabited 128e93f3754c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L341-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L341-L348

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowHeightLowerBound_hyps_inhabited_128e93f3754c :
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧
      IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1
        (map (Rat.castHom ℂ) (detForm ℚ)) ∧
      ∃ G : Set (Fin 2 → ℤ), Submodule.span ℤ G = ⊤ ∧
        ∀ u ∈ G, formNorm (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun i => (u i : ℂ)) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ArithBezout».«ChowHeightLowerBound».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowHeightLowerBound_hyps_inhabited_128e93f3754c
