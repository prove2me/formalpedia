-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocFlat_DoubleStepProof_rowE_inv__be53a7a31087
-- name    : P2M_GlobalTheory_LocFlat_DoubleStepProof_rowE_inv__be53a7a31087
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:28:02.780841+00:00
-- url     : https://prove2.me/theorems/f3f011e6-724b-5fa2-86a8-cef8d3c711ce
-- title:
--   P2 M Global Theory Loc Flat Double Step Proof row E inv  be53a7a31087: P2 M Global Theory Loc Flat Double Step Proof row E inv  be53a7a31087
-- statement:
--   The P2 M Global Theory Loc Flat Double Step Proof row E inv  be53a7a31087 construction uses the P2 M Global Theory Loc Flat Double Step Proof row E inv  be53a7a31087 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymLevelDoubleStepOfFlatColumnFlatRow.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymLevelDoubleStepOfFlatColumnFlatRow.lean#L118-L126

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

theorem P2M_GlobalTheory_LocFlat_DoubleStepProof_rowE_inv__be53a7a31087 {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (u : n → k) :
    (rowE c p u)⁻¹ = rowE c p (-u) := by sorry

alias «GlobalTheory».«LocFlat».«DoubleStepProof».«rowE_inv'» := P2M_GlobalTheory_LocFlat_DoubleStepProof_rowE_inv__be53a7a31087
