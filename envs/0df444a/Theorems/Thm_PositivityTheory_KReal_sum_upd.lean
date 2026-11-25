-- Prove2me | Theorems.Thm_PositivityTheory_KReal_sum_upd
-- name    : PositivityTheory.KReal.sum_upd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:06.570552+00:00
-- url     : https://prove2.me/theorems/062ae3e7-539a-43aa-9f11-488c3b575569
-- title:
--   KReal: sum upd
-- statement:
--   The KReal construction uses the sum upd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasC.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasC.lean#L20-L27

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem PositivityTheory.KReal.sum_upd {β : Type} [AddCommMonoid β] (s : J) (g : (J → I) → I → β) :
    ∑ w, ∑ j, g w j = ∑ w, ∑ j, g (Function.update w s j) (w s) := by sorry
