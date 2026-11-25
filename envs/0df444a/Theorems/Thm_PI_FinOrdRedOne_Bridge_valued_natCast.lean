-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Bridge_valued_natCast
-- name    : PI.FinOrdRedOne.Bridge.valued_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:44.457193+00:00
-- url     : https://prove2.me/theorems/919a3ee5-49fa-4f5c-8f7e-c5c64bf119a8
-- title:
--   Bridge: valued nat Cast
-- statement:
--   The Bridge construction uses the valued nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L51-L57

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

theorem PI.FinOrdRedOne.Bridge.valued_natCast (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    Valued.v ((p : ℕ) : P.adicCompletion E) = exp (-1 : ℤ) := by sorry
