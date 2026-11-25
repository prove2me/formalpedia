-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SymLevelExists_toBlocks___mul_embX_f9431060e73d
-- name    : P2M_GlobalTheory_SymLevelExists_toBlocks___mul_embX_f9431060e73d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:08.382136+00:00
-- url     : https://prove2.me/theorems/b65778a7-46a0-43b5-92d2-90468bcf31c5
-- title:
--   P2 M Global Theory Sym Level Exists to Blocks   mul emb X f9431060e73d: P2 M Global Theory Sym Level Exists to Blocks   mul emb X f9431060e73d
-- statement:
--   The P2 M Global Theory Sym Level Exists to Blocks   mul emb X f9431060e73d construction uses the P2 M Global Theory Sym Level Exists to Blocks   mul emb X f9431060e73d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsSymmetricPositionLevel.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsSymmetricPositionLevel.lean#L34-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymLevelExists
variable {F : Type} [Field F] {κ l : ℕ}

theorem P2M_GlobalTheory_SymLevelExists_toBlocks___mul_embX_f9431060e73d {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    (u * embX l γ).val.toBlocks₁₁ = γ.val := by sorry

alias «GlobalTheory».«SymLevelExists».«toBlocks₁₁_mul_embX» := P2M_GlobalTheory_SymLevelExists_toBlocks___mul_embX_f9431060e73d
