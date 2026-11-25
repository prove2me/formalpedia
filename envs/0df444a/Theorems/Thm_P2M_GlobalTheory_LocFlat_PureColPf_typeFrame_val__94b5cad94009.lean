-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_val__94b5cad94009
-- name    : P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_val__94b5cad94009
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:08.313868+00:00
-- url     : https://prove2.me/theorems/a367efc0-801a-5f9d-84d0-72822e06668e
-- title:
--   P2 M Global Theory Loc Flat Pure Col Pf type Frame val  94b5cad94009: P2 M Global Theory Loc Flat Pure Col Pf type Frame val  94b5cad94009
-- statement:
--   The P2 M Global Theory Loc Flat Pure Col Pf type Frame val  94b5cad94009 construction uses the P2 M Global Theory Loc Flat Pure Col Pf type Frame val  94b5cad94009 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
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
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] {n n' ι ι' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

theorem P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_val__94b5cad94009 (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by sorry

alias «GlobalTheory».«LocFlat».«PureColPf».«typeFrame_val'» := P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_val__94b5cad94009
