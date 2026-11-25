-- Prove2me | Theorems.Thm_PositivityTheory_Gud_Pf_list_symmetric_pair_decomposition
-- name    : PositivityTheory.Gud.Pf.list_symmetric_pair_decomposition
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:48:03.868456+00:00
-- url     : https://prove2.me/theorems/9bdeb65b-78ca-41e5-8e4a-3d313698c5aa
-- title:
--   Pf: list symmetric pair decomposition
-- statement:
--   The Pf construction uses the list symmetric pair decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/UnitaryDualGL/GenericUnitaryDual/PComb.lean#L5-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/UnitaryDualGL/GenericUnitaryDual/PComb.lean#L5-L64

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

theorem PositivityTheory.Gud.Pf.list_symmetric_pair_decomposition {α : Type*} : ∀ (n : ℕ) (l : List (α × ℝ)), l.length = n →
    List.Perm (l.map (fun p => (p.1, -p.2))) l →
    ∃ (a : List α) (b : List (α × ℝ)), (∀ p ∈ b, 0 < p.2 ∧ p ∈ l) ∧
      List.Perm (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p => [p, (p.1, -p.2)])) l := by sorry
