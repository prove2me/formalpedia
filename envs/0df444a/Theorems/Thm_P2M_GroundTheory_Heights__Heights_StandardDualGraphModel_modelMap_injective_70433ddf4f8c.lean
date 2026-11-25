-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_injective_70433ddf4f8c
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_injective_70433ddf4f8c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:57.063582+00:00
-- url     : https://prove2.me/theorems/1056672b-2627-4fca-b005-69b4b6e9b5b4
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Graph Model model Map injective 70433ddf4f8c: P2 M Ground Theory Heights  Heights Standard Dual Graph Model model Map injective 70433ddf4f8c
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Graph Model model Map injective 70433ddf4f8c construction uses the P2 M Ground Theory Heights  Heights Standard Dual Graph Model model Map injective 70433ddf4f8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L46-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGraphModel
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualGraphModel
open StandardDualImageBottom
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_injective_70433ddf4f8c (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (modelMap b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualGraphModel».«modelMap_injective» := P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_injective_70433ddf4f8c
