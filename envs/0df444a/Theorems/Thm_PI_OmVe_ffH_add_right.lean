-- Prove2me | Theorems.Thm_PI_OmVe_ffH_add_right
-- name    : PI.OmVe.ffH_add_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:00:59.508868+00:00
-- url     : https://prove2.me/theorems/07ce8cac-9cf7-41b2-b299-a91a3dc0a5e1
-- title:
--   Om Ve: ff H add right
-- statement:
--   The Om Ve construction uses the ff H add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean#L14-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
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
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

theorem PI.OmVe.ffH_add_right (x y z : Fin M → K) : ffH σ J x (y + z) = ffH σ J x y + ffH σ J x z := by sorry
