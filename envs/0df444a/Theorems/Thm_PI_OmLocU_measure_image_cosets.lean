-- Prove2me | Theorems.Thm_PI_OmLocU_measure_image_cosets
-- name    : PI.OmLocU.measure_image_cosets
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:05:00.985234+00:00
-- url     : https://prove2.me/theorems/ed8aaabc-54eb-41fc-bd28-26322e9d0a8c
-- title:
--   Om Loc U: measure image cosets
-- statement:
--   The Om Loc U construction uses the measure image cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/MeasureImageCosets.lean#L9-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/MeasureImageCosets.lean#L9-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_MeasureImageCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU
open MeasureTheory

theorem PI.OmLocU.measure_image_cosets {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (H L : AddSubgroup V) (hHL : H ≤ L)
    (hH : MeasurableSet (H : Set V)) (hfin : H.relIndex L ≠ 0) (S : Set L)
    (hS : ∀ x ∈ S, ∀ y : L, (y : V) ∈ H → x + y ∈ S) :
    μ (((↑) : L → V) '' S) =
      (Nat.card (QuotientAddGroup.mk '' S : Set (L ⧸ H.addSubgroupOf L)) : ENNReal) * μ H := by sorry
