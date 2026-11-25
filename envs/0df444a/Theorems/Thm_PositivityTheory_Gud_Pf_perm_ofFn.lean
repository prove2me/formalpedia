-- Prove2me | Theorems.Thm_PositivityTheory_Gud_Pf_perm_ofFn
-- name    : PositivityTheory.Gud.Pf.perm_ofFn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:50.31412+00:00
-- url     : https://prove2.me/theorems/5eb2a9bb-98a7-5166-beda-7fb308a35cc4
-- title:
--   Pf: perm of Fn
-- statement:
--   The Pf construction uses the perm of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/UnitaryDualGL/GenericUnitaryDual/PComb.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/UnitaryDualGL/GenericUnitaryDual/PComb.lean#L70-L86

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitaryDualGL_GenericUnitaryDual_PComb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Gud PositivityTheory.Gud.Pf

theorem PositivityTheory.Gud.Pf.perm_ofFn {β : Type*} {h : ℕ} (x : Fin h → β) (l : List β) (hp : List.Perm l (List.ofFn x)) :
    ∃ (y : Fin h → β), List.ofFn y = l ∧ ∃ σ : Equiv.Perm (Fin h), y = fun j => x (σ j) := by sorry
