-- Prove2me | Theorems.Thm_PI_VolStabW_FFHS_perp_sub_mem
-- name    : PI.VolStabW.FFHS.perp_sub_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:53.431543+00:00
-- url     : https://prove2.me/theorems/457e36b7-1467-5ffa-b283-d2aa76be0afe
-- title:
--   FFHS: perp sub mem
-- statement:
--   The FFHS construction uses the perp sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFCnt.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFCnt.lean#L12-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem PI.VolStabW.FFHS.perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by sorry
