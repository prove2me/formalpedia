-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_specInt_hypotheses_hold_828f2dced2c2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_specInt_hypotheses_hold_828f2dced2c2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:34.807173+00:00
-- url     : https://prove2.me/theorems/7c85a677-70c9-4d18-8e32-b4361323edd0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter spec Int hypotheses hold 828f2dced2c2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter spec Int hypoth
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter spec Int hypotheses hold 828f2dced2c2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter spec Int hypotheses hold 828f2dced2c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean#L199-L201

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_specInt_hypotheses_hold_828f2dced2c2 : IsArithVar (⊥ : Ideal (MRing (GlobalTheory 1))) 1 ∧ IsSmoothHerm (fsO1 1) ∧
    IsSec (⊥ : Ideal (MRing (GlobalTheory 1))) (fsO1 1) (Xb 1 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«specInt_hypotheses_hold» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_specInt_hypotheses_hold_828f2dced2c2
