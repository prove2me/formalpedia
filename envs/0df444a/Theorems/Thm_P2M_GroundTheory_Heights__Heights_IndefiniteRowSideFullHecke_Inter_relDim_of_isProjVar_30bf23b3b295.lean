-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_relDim_of_isProjVar_30bf23b3b295
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_relDim_of_isProjVar_30bf23b3b295
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:53:47.571929+00:00
-- url     : https://prove2.me/theorems/9e1be358-f7d4-4c3c-83bf-f943d1ed8184
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rel Dim of is Proj Var 30bf23b3b295: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rel Dim of is Pro
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rel Dim of is Proj Var 30bf23b3b295 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rel Dim of is Proj Var 30bf23b3b295 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CompsDim.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CompsDim.lean#L20-L27

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_relDim_of_isProjVar_30bf23b3b295 {P : Ideal (MRing ι ℂ)} {e : ℕ} (h : IsProjVar P e) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = (e : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«relDim_of_isProjVar» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_relDim_of_isProjVar_30bf23b3b295
