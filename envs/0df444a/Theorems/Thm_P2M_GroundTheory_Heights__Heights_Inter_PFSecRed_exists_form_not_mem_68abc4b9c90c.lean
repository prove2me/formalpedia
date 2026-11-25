-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFSecRed_exists_form_not_mem_68abc4b9c90c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFSecRed_exists_form_not_mem_68abc4b9c90c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:17.204655+00:00
-- url     : https://prove2.me/theorems/1dabbd3c-e121-4f08-87af-d2301f518a1c
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFSec Red exists form not mem 68abc4b9c90c: P2 M Ground Theory Heights  Heights Inter PFSec Red exists form not mem 68abc4b9c90c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFSec Red exists form not mem 68abc4b9c90c construction uses the P2 M Ground Theory Heights  Heights Inter PFSec Red exists form not mem 68abc4b9c90c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFSecRed.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFSecRed.lean#L13-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFSecRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFSecRed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_PFSecRed_exists_form_not_mem_68abc4b9c90c {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) (c : K → ℕ) :
    ∃ s : MRing ι, IsMultiHomog s c ∧ s ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFSecRed».«exists_form_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_PFSecRed_exists_form_not_mem_68abc4b9c90c
