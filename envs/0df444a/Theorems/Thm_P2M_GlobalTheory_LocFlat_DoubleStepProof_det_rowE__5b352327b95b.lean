-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocFlat_DoubleStepProof_det_rowE__5b352327b95b
-- name    : P2M_GlobalTheory_LocFlat_DoubleStepProof_det_rowE__5b352327b95b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:32:05.161415+00:00
-- url     : https://prove2.me/theorems/2d492f4f-2786-41e2-a226-afdaa67e07e7
-- title:
--   P2 M Global Theory Loc Flat Double Step Proof det row E  5b352327b95b: P2 M Global Theory Loc Flat Double Step Proof det row E  5b352327b95b
-- statement:
--   The P2 M Global Theory Loc Flat Double Step Proof det row E  5b352327b95b construction uses the P2 M Global Theory Loc Flat Double Step Proof det row E  5b352327b95b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymLevelDoubleStepOfFlatColumnFlatRow.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymLevelDoubleStepOfFlatColumnFlatRow.lean#L128-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.DoubleStepProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem P2M_GlobalTheory_LocFlat_DoubleStepProof_det_rowE__5b352327b95b {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (u : n → k) :
    Matrix.GeneralLinearGroup.det (rowE c p u) = 1 := by sorry

alias «GlobalTheory».«LocFlat».«DoubleStepProof».«det_rowE'» := P2M_GlobalTheory_LocFlat_DoubleStepProof_det_rowE__5b352327b95b
