-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVar_of_mem_comps_e9b859fb85c1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVar_of_mem_comps_e9b859fb85c1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:54:01.920133+00:00
-- url     : https://prove2.me/theorems/7e792cb9-672e-4330-ab41-43ee7fb3cffc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var of mem comps e9b859fb85c1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var of
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var of mem comps e9b859fb85c1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var of mem comps e9b859fb85c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CompsDim.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CompsDim.lean#L29-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPrincipalDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CompsDim
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  blockWeight)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVar_of_mem_comps_e9b859fb85c1 {P : Ideal (MRing ι ℂ)} {e : ℕ} {s : MRing ι ℂ} {c : K → ℕ}
    (hP : IsProjVar P (e + 1)) (hs : IsMultiHomog s c) (hsP : s ∉ P) {W : Ideal (MRing ι ℂ)}
    (hW : W ∈ comps P s) : IsProjVar W e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isProjVar_of_mem_comps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVar_of_mem_comps_e9b859fb85c1
