-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Bridge_eq_zero_of_forall_dvd
-- name    : PI.FinOrdRedOne.Bridge.eq_zero_of_forall_dvd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:53.32372+00:00
-- url     : https://prove2.me/theorems/85a1195a-cf8e-459f-acb7-3652b95dd43a
-- title:
--   Bridge: eq zero of forall dvd
-- statement:
--   The Bridge construction uses the eq zero of forall dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L104-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L104-L112

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

theorem PI.FinOrdRedOne.Bridge.eq_zero_of_forall_dvd (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) (x : OP E P)
    (hx : ∀ k : ℕ, ((p : ℕ) : OP E P) ^ k ∣ x) : x = 0 := by sorry
