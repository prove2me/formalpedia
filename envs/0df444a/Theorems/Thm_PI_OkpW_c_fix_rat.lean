-- Prove2me | Theorems.Thm_PI_OkpW_c_fix_rat
-- name    : PI.OkpW.c_fix_rat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:14:46.004644+00:00
-- url     : https://prove2.me/theorems/af4f1f1e-f77b-43a6-9597-87c2a78a575f
-- title:
--   Okp W: c fix rat
-- statement:
--   The Okp W construction uses the c fix rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/CFixRat.lean#L28-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/CFixRat.lean#L28-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFixRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {K : Type} [Field K] [NumberField K]

theorem PI.OkpW.c_fix_rat (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) {y : K}
    (hy : c y = y) : ∃ r : ℚ, (r : K) = y := by sorry
