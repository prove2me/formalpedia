-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Bridge_intValuation_natCast
-- name    : PI.FinOrdRedOne.Bridge.intValuation_natCast
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:58.64516+00:00
-- url     : https://prove2.me/theorems/8dd28be2-134c-4263-8022-707dc5acd189
-- title:
--   Bridge: int Valuation nat Cast
-- statement:
--   The Bridge construction uses the int Valuation nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L37-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L37-L49

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

theorem PI.FinOrdRedOne.Bridge.intValuation_natCast (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    P.intValuation (p : 𝓞 E) = exp (-1 : ℤ) := by sorry
