-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_injective_3c532cdb708d
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_injective_3c532cdb708d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:18.578175+00:00
-- url     : https://prove2.me/theorems/2cdc9ad1-fc75-40c3-a848-6133a871ecad
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Graph Model cone Lift injective 3c532cdb708d: P2 M Ground Theory Heights  Heights Standard Dual Graph Model cone Lift injective 3c532cdb708d
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Graph Model cone Lift injective 3c532cdb708d construction uses the P2 M Ground Theory Heights  Heights Standard Dual Graph Model cone Lift injective 3c532cdb708d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L37-L39

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_injective_3c532cdb708d (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (coneLift b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualGraphModel».«coneLift_injective» := P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_injective_3c532cdb708d
