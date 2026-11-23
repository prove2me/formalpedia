-- Prove2me | Theorems.Thm_PI_ZW_zeta1_eq_sub_one_mul_riemannZeta_of_ne_one
-- name    : PI.ZW.zeta1_eq_sub_one_mul_riemannZeta_of_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:00.856603+00:00
-- url     : https://prove2.me/theorems/9996b93b-397d-4f31-998f-1f40e9224b3a
-- title:
--   ZW: zeta1 eq sub one mul riemann Zeta of ne one
-- statement:
--   The ZW construction uses the zeta1 eq sub one mul riemann Zeta of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightOne.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightOne.lean#L11-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex Filter Topology
open PI PI.ZW

theorem PI.ZW.zeta1_eq_sub_one_mul_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : zeta1 s = (s - 1) * riemannZeta s := by sorry
