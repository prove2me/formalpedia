-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_inv_val__6c94e0f85deb
-- name    : P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_inv_val__6c94e0f85deb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:10.143706+00:00
-- url     : https://prove2.me/theorems/9cb91350-397f-4797-a6ba-ba240bf93e56
-- title:
--   P2 M Global Theory Loc Flat Pure Col Pf type Frame inv val  6c94e0f85deb: P2 M Global Theory Loc Flat Pure Col Pf type Frame inv val  6c94e0f85deb
-- statement:
--   The P2 M Global Theory Loc Flat Pure Col Pf type Frame inv val  6c94e0f85deb construction uses the P2 M Global Theory Loc Flat Pure Col Pf type Frame inv val  6c94e0f85deb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L18-L25

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

theorem P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_inv_val__6c94e0f85deb (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by sorry

alias «GlobalTheory».«LocFlat».«PureColPf».«typeFrame_inv_val'» := P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_inv_val__6c94e0f85deb
