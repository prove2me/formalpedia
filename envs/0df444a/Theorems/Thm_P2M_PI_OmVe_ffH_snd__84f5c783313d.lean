-- Prove2me | Theorems.Thm_P2M_PI_OmVe_ffH_snd__84f5c783313d
-- name    : P2M_PI_OmVe_ffH_snd__84f5c783313d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:20.98501+00:00
-- url     : https://prove2.me/theorems/00314c0a-36f0-5f80-a129-830ca11a3bf7
-- title:
--   P2 M PI Om Ve ff H snd  84f5c783313d: P2 M PI Om Ve ff H snd  84f5c783313d
-- statement:
--   The P2 M PI Om Ve ff H snd  84f5c783313d construction uses the P2 M PI Om Ve ff H snd  84f5c783313d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/FfHSelfOfSnd.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/FfHSelfOfSnd.lean#L18-L20

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

theorem P2M_PI_OmVe_ffH_snd__84f5c783313d (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).2 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).2 * (x l).2 := by sorry

alias «PI».«OmVe».«ffH_snd'» := P2M_PI_OmVe_ffH_snd__84f5c783313d
