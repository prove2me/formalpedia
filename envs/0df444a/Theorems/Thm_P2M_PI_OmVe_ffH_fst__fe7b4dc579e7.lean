-- Prove2me | Theorems.Thm_P2M_PI_OmVe_ffH_fst__fe7b4dc579e7
-- name    : P2M_PI_OmVe_ffH_fst__fe7b4dc579e7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:10.610097+00:00
-- url     : https://prove2.me/theorems/e4e64cb9-4bc3-5997-b250-7cbf44319528
-- title:
--   P2 M PI Om Ve ff H fst  fe7b4dc579e7: P2 M PI Om Ve ff H fst  fe7b4dc579e7
-- statement:
--   The P2 M PI Om Ve ff H fst  fe7b4dc579e7 construction uses the P2 M PI Om Ve ff H fst  fe7b4dc579e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/FfHSelfOfSnd.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/FfHSelfOfSnd.lean#L14-L16

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

theorem P2M_PI_OmVe_ffH_fst__fe7b4dc579e7 (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).1 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).1 * (x l).1 := by sorry

alias «PI».«OmVe».«ffH_fst'» := P2M_PI_OmVe_ffH_fst__fe7b4dc579e7
