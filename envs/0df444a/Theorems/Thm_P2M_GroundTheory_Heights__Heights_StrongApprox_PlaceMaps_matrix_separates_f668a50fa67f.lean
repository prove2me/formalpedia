-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_matrix_separates_f668a50fa67f
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_matrix_separates_f668a50fa67f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:40:15.729252+00:00
-- url     : https://prove2.me/theorems/418c0c50-9be6-49b5-b0fe-6a8210fe2829
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps matrix separates f668a50fa67f: P2 M Ground Theory Heights  Heights Strong Approx Place Maps matrix separates f668a50fa67f
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps matrix separates f668a50fa67f construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps matrix separates f668a50fa67f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L152-L155

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_matrix_separates_f668a50fa67f {N : ℕ} (X Y : Matrix (Fin N) (Fin N) (AE F E))
    (h : ∀ v, X.map (compAt E v) = Y.map (compAt E v)) : X = Y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«matrix_separates» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_matrix_separates_f668a50fa67f
