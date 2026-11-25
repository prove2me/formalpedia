-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_form_a0e783e68924
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_form_a0e783e68924
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:02:34.478867+00:00
-- url     : https://prove2.me/theorems/59e4c963-b894-440e-b35d-a8e20fe55e0a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists form a0e783e68924: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists form a0e783e68924
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists form a0e783e68924 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists form a0e783e68924 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CompsDim.lean#L49-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CompsDim.lean#L49-L64

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_form_a0e783e68924 {P : Ideal (MRing ι ℂ)} (hP : IsMultiProjPrime P) (c : K → ℕ) :
    ∃ s : MRing ι ℂ, IsMultiHomog s c ∧ s ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«exists_form» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_form_a0e783e68924
