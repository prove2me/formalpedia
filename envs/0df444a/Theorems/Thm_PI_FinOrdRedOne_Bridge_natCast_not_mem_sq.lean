-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Bridge_natCast_not_mem_sq
-- name    : PI.FinOrdRedOne.Bridge.natCast_not_mem_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:52.222885+00:00
-- url     : https://prove2.me/theorems/565f98a1-e304-5c66-bb84-f6896ed3d117
-- title:
--   Bridge: nat Cast not mem sq
-- statement:
--   The Bridge construction uses the nat Cast not mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/Bridge.lean#L12-L35

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

theorem PI.FinOrdRedOne.Bridge.natCast_not_mem_sq (p : ℕ) (hp : p.Prime) (hU : Unram E p) (P : HeightOneSpectrum (𝓞 E))
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) : (p : 𝓞 E) ∉ P.asIdeal ^ 2 := by sorry
