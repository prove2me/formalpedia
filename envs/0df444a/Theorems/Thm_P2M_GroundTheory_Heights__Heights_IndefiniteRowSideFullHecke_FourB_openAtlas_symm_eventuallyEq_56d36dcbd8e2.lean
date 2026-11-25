-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_symm_eventuallyEq_56d36dcbd8e2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_symm_eventuallyEq_56d36dcbd8e2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:40:51.520801+00:00
-- url     : https://prove2.me/theorems/96887b80-d8e0-5dd5-86f5-d9d989a0a232
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas symm eventually Eq 56d36dcbd8e2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas symm eventually Eq 56d36dcbd8e2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas symm eventually Eq 56d36dcbd8e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OpenAtlasSymmEventuallyEq.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OpenAtlasSymmEventuallyEq.lean#L28-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_symm_eventuallyEq_56d36dcbd8e2 {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ))
    (hΩ : Nonempty Ω) (j : Fin (openAtlas Ω hΩ).n) (F : (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hy : y ∈ Ω) :
    (fun z => F (((openAtlas Ω hΩ).chart j).symm z : Fin D → ℂ)) =ᶠ[𝓝 y] F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«openAtlas_symm_eventuallyEq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_symm_eventuallyEq_56d36dcbd8e2
