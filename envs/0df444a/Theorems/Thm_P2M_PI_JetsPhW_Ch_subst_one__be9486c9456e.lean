-- Prove2me | Theorems.Thm_P2M_PI_JetsPhW_Ch_subst_one__be9486c9456e
-- name    : P2M_PI_JetsPhW_Ch_subst_one__be9486c9456e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:40.34685+00:00
-- url     : https://prove2.me/theorems/28b3c66c-08f1-4053-bb16-ab7a0c633fa4
-- title:
--   P2 M PI Jets Ph W Ch subst one  be9486c9456e: P2 M PI Jets Ph W Ch subst one  be9486c9456e
-- statement:
--   The P2 M PI Jets Ph W Ch subst one  be9486c9456e construction uses the P2 M PI Jets Ph W Ch subst one  be9486c9456e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean#L101-L102

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.JetsPhW
open PI PI.JetsPhW PI.JetsPhW.Ch
variable {R : Type*} [CommRing R] {σ : Type*}

theorem P2M_PI_JetsPhW_Ch_subst_one__be9486c9456e (a : MvPowerSeries σ R) : PowerSeries.subst a (1 : PowerSeries R) = 1 := by sorry

alias «PI».«JetsPhW».«Ch».«subst_one'» := P2M_PI_JetsPhW_Ch_subst_one__be9486c9456e
