-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Bridge_maximalIdeal_eq
-- name    : PI.FinOrdRedOne.Bridge.maximalIdeal_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:42.573842+00:00
-- url     : https://prove2.me/theorems/2203be55-2e84-4df5-b8a6-1a47584c2a1d
-- title:
--   Bridge: maximal Ideal eq
-- statement:
--   The Bridge construction uses the maximal Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L69-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L69-L102

import Definitions.Def_Formalism_PeriodIntegrals_FinOrdRedOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_Bridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Bridge
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Ideal WithZero
variable {E : Type} [Field E] [NumberField E]

theorem PI.FinOrdRedOne.Bridge.maximalIdeal_eq (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    IsLocalRing.maximalIdeal (OP E P) = span {((p : ℕ) : OP E P)} := by sorry
