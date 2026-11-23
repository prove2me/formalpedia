-- Prove2me | Theorems.Thm_PI_OkpW_natCard_quot
-- name    : PI.OkpW.natCard_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:41.523771+00:00
-- url     : https://prove2.me/theorems/ec8ae8b6-2d2f-43de-b4d3-b4814d7cb9de
-- title:
--   Okp W: nat Card quot
-- statement:
--   The Okp W construction uses the nat Card quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L71-L78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
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
variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]

theorem PI.OkpW.natCard_quot (hK : Module.finrank ℚ K = 2) :
    Nat.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by sorry
