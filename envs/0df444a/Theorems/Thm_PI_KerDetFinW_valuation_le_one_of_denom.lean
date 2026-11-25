-- Prove2me | Theorems.Thm_PI_KerDetFinW_valuation_le_one_of_denom
-- name    : PI.KerDetFinW.valuation_le_one_of_denom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:30.298107+00:00
-- url     : https://prove2.me/theorems/96c30dad-7207-519f-baf8-ce8e8ec6159a
-- title:
--   Ker Det Fin W: valuation le one of denom
-- statement:
--   The Ker Det Fin W construction uses the valuation le one of denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ValuationLeOneOfDenom.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ValuationLeOneOfDenom.lean#L55-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso

theorem PI.KerDetFinW.valuation_le_one_of_denom {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p U : ℕ}
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) {x : K}
    (hx : (U : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by sorry
