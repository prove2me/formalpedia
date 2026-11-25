-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchSheetAE_volume_preimage_null_9a44d12a3b9a
-- name    : P2M_GroundTheory_Heights__Heights_BranchSheetAE_volume_preimage_null_9a44d12a3b9a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:26.236788+00:00
-- url     : https://prove2.me/theorems/078f7045-539b-477c-b1e4-ccb8986eda04
-- title:
--   P2 M Ground Theory Heights  Heights Branch Sheet AE volume preimage null 9a44d12a3b9a: P2 M Ground Theory Heights  Heights Branch Sheet AE volume preimage null 9a44d12a3b9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch Sheet AE volume preimage null 9a44d12a3b9a construction uses the P2 M Ground Theory Heights  Heights Branch Sheet AE volume preimage null 9a44d12a3b9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchSheetAE.lean#L20-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchSheetAE.lean#L20-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRankDeficientFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscriminantSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchSheetAE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.BranchSheetAE
variable {d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_BranchSheetAE_volume_preimage_null_9a44d12a3b9a {G : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ} (hG : IsOpen G)
    (hF : DifferentiableOn ℂ F G) (hdet : ∀ w ∈ G, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0)
    {N : Set (Fin d → ℂ)} (hN : volume N = 0) :
    volume {t | t ∈ G ∧ F t ∈ N} = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchSheetAE».«volume_preimage_null» := P2M_GroundTheory_Heights__Heights_BranchSheetAE_volume_preimage_null_9a44d12a3b9a
