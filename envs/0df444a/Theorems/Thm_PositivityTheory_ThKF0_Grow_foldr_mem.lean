-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Grow_foldr_mem
-- name    : PositivityTheory.ThKF0.Grow.foldr_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:23.081798+00:00
-- url     : https://prove2.me/theorems/65e1ca1a-fb6e-4fdb-85c3-9e83c2196e34
-- title:
--   Grow: foldr mem
-- statement:
--   The Grow construction uses the foldr mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L55-L59

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal
open MeasureTheory
variable {X W : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
omit [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem PositivityTheory.ThKF0.Grow.foldr_mem {S : Set (X → ℂ)} {dd : W → (X → ℂ) → X → ℂ} (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (l : List W) {Θ : X → ℂ}
    (h : Θ ∈ S) : l.foldr dd Θ ∈ S := by sorry
