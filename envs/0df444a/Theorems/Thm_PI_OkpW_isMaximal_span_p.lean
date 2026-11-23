-- Prove2me | Theorems.Thm_PI_OkpW_isMaximal_span_p
-- name    : PI.OkpW.isMaximal_span_p
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:38.937188+00:00
-- url     : https://prove2.me/theorems/e8007ba1-7d05-485e-872e-b07a99331af9
-- title:
--   Okp W: is Maximal span p
-- statement:
--   The Okp W construction uses the is Maximal span p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L67-L69

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

theorem PI.OkpW.isMaximal_span_p (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) :
    (Ideal.span {(p : 𝓞 K)}).IsMaximal := by sorry
