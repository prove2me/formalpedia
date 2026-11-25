-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_segre_f966ae4bfd55
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_segre_f966ae4bfd55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:04.594345+00:00
-- url     : https://prove2.me/theorems/3d0953ef-cc41-4e36-8d3f-8df3dd0dabfa
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists is Section On segre f966ae4bfd55: P2 M Ground Theory Heights  Heights Inter Thm IExists is Section On segre f966ae4bfd55
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists is Section On segre f966ae4bfd55 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists is Section On segre f966ae4bfd55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L105-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_segre_f966ae4bfd55 {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (m : ℕ) :
    IsSectionOn P (segreLine m) (secOf P fun _ => m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«isSectionOn_segre» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_segre_f966ae4bfd55
