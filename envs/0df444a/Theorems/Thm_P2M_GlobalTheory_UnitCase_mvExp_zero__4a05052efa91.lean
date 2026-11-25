-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitCase_mvExp_zero__4a05052efa91
-- name    : P2M_GlobalTheory_UnitCase_mvExp_zero__4a05052efa91
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:38:55.992712+00:00
-- url     : https://prove2.me/theorems/5e77985c-3bb2-460d-be19-f1ea1439c7c7
-- title:
--   P2 M Global Theory Unit Case mv Exp zero  4a05052efa91: P2 M Global Theory Unit Case mv Exp zero  4a05052efa91
-- statement:
--   The P2 M Global Theory Unit Case mv Exp zero  4a05052efa91 construction uses the P2 M Global Theory Unit Case mv Exp zero  4a05052efa91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L83-L87

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}

theorem P2M_GlobalTheory_UnitCase_mvExp_zero__4a05052efa91 : mvExp (0 : MvPowerSeries σ C) = 1 := by sorry

alias «GlobalTheory».«UnitCase».«mvExp_zero'» := P2M_GlobalTheory_UnitCase_mvExp_zero__4a05052efa91
