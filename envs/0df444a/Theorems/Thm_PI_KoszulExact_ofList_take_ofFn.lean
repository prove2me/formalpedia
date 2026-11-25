-- Prove2me | Theorems.Thm_PI_KoszulExact_ofList_take_ofFn
-- name    : PI.KoszulExact.ofList_take_ofFn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:33:52.727912+00:00
-- url     : https://prove2.me/theorems/6f0bdf8f-dfc6-4cc1-b296-0f0ff2f87726
-- title:
--   Koszul Exact: of List take of Fn
-- statement:
--   The Koszul Exact construction uses the of List take of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/OfListTakeOfFn.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/OfListTakeOfFn.lean#L12-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_OfListTakeOfFn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
open RingTheory.Sequence

theorem PI.KoszulExact.ofList_take_ofFn {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn s).take i) = Ii s i := by sorry
