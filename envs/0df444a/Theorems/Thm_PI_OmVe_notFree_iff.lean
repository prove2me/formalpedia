-- Prove2me | Theorems.Thm_PI_OmVe_notFree_iff
-- name    : PI.OmVe.notFree_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:41.629635+00:00
-- url     : https://prove2.me/theorems/4d8ba224-b9e0-440d-9a01-e9c8e790d496
-- title:
--   Om Ve: not Free iff
-- statement:
--   The Om Ve construction uses the not Free iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/FfHSelfOfSnd.lean#L36-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/FfHSelfOfSnd.lean#L36-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_FfHSelfOfSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))

theorem PI.OmVe.notFree_iff (x : Fin M → k × k) :
    (¬ ∀ c : k × k, c • x = 0 → c = 0) ↔ (∀ l, (x l).1 = 0) ∨ (∀ l, (x l).2 = 0) := by sorry
