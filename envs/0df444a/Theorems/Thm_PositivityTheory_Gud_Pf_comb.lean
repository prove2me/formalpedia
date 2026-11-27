-- Prove2me | Theorems.Thm_PositivityTheory_Gud_Pf_comb
-- name    : PositivityTheory.Gud.Pf.comb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:46.115862+00:00
-- url     : https://prove2.me/theorems/db8e76cd-91d2-5320-b1bc-b386c7bf30c2
-- title:
--   Pf: comb
-- statement:
--   The Pf construction uses the comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/UnitaryDualGL/GenericUnitaryDual/PComb.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/UnitaryDualGL/GenericUnitaryDual/PComb.lean#L66-L68

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

theorem PositivityTheory.Gud.Pf.comb {α : Type*} (l : List (α × ℝ)) (hl : List.Perm (l.map (fun p => (p.1, -p.2))) l) :
    ∃ (a : List α) (b : List (α × ℝ)), (∀ p ∈ b, 0 < p.2 ∧ p ∈ l) ∧
      List.Perm (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p => [p, (p.1, -p.2)])) l := by sorry
