-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_pos_of_mem_divSupp_5458a53f671d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_pos_of_mem_divSupp_5458a53f671d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:29.646573+00:00
-- url     : https://prove2.me/theorems/17a5ea2d-182c-5174-b803-7533925411f1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter mult At pos of mem div Supp 5458a53f671d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter mult At pos
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter mult At pos of mem div Supp 5458a53f671d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter mult At pos of mem div Supp 5458a53f671d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtPosOfMemDivSupp.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtPosOfMemDivSupp.lean#L16-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtPosOfMemDivSupp
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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_pos_of_mem_divSupp_5458a53f671d {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp P s) : 0 < multAt (P ⊔ Ideal.span {s}) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«multAt_pos_of_mem_divSupp» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_pos_of_mem_divSupp_5458a53f671d
