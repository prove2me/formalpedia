-- Prove2me | Theorems.Thm_PI_OmVe_perp_surj
-- name    : PI.OmVe.perp_surj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:29:01.20286+00:00
-- url     : https://prove2.me/theorems/397408fe-62b2-46c0-b769-de74948b7612
-- title:
--   Om Ve: perp surj
-- statement:
--   The Om Ve construction uses the perp surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/FfHSelfOfSnd.lean#L64-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/FfHSelfOfSnd.lean#L64-L88

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

theorem PI.OmVe.perp_surj {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) (w : Fin a' → k × k) :
    ∃ x : Fin M → k × k, ∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = w j := by sorry
