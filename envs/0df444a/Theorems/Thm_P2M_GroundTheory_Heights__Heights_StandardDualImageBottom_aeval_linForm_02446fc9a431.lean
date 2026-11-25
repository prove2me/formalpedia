-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_linForm_02446fc9a431
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_linForm_02446fc9a431
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:36.167095+00:00
-- url     : https://prove2.me/theorems/9e24d47c-8cba-400e-ba9e-35db101e497c
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Image Bottom aeval lin Form 02446fc9a431: P2 M Ground Theory Heights  Heights Standard Dual Image Bottom aeval lin Form 02446fc9a431
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Image Bottom aeval lin Form 02446fc9a431 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Image Bottom aeval lin Form 02446fc9a431 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdImageBot.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdImageBot.lean#L42-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
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
open GroundTheory.Heights₂.Heights.StandardDualImageBottom
open DualArithmeticVariety
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_linForm_02446fc9a431 (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (q : Σ _ : Unit, Fin i) :
    aeval (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) = genPt K i q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualImageBottom».«aeval_linForm» := P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_linForm_02446fc9a431
