-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_mk_fc8d5b72f0f1
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_mk_fc8d5b72f0f1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:22.394895+00:00
-- url     : https://prove2.me/theorems/23aa34ea-a153-4c29-b2a0-985ff0105a0c
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Graph Model cone Lift mk fc8d5b72f0f1: P2 M Ground Theory Heights  Heights Standard Dual Graph Model cone Lift mk fc8d5b72f0f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Graph Model cone Lift mk fc8d5b72f0f1 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Graph Model cone Lift mk fc8d5b72f0f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L32-L34

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_mk_fc8d5b72f0f1 (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (dualBlocks T)) :
    coneLift b (Ideal.Quotient.mk _ f) = mConeMap (dualLatticeCoord b) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualGraphModel».«coneLift_mk» := P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_mk_fc8d5b72f0f1
