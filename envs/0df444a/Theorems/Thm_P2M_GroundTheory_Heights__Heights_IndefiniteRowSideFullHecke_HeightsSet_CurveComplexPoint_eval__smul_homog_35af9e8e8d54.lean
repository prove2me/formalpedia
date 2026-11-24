-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_eval__smul_homog_35af9e8e8d54
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_eval__smul_homog_35af9e8e8d54
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:19.598007+00:00
-- url     : https://prove2.me/theorems/fe49530d-07b0-4d59-881d-a09a182854ca
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Complex Point eval  smul homog 35af9e8e8d54: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hei
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Complex Point eval  smul homog 35af9e8e8d54 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Complex Point eval  smul homog 35af9e8e8d54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveComplexPoint.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveComplexPoint.lean#L13-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_eval__smul_homog_35af9e8e8d54 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F : Type*} [CommRing F] (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a)
    (c : K → F) (y : (Σ k, ι k) → F) :
    eval₂ (Int.castRingHom F) (fun p => c p.1 * y p) f =
      (∏ k, c k ^ a k) * eval₂ (Int.castRingHom F) y f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«CurveComplexPoint».«eval₂_smul_homog» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_eval__smul_homog_35af9e8e8d54
