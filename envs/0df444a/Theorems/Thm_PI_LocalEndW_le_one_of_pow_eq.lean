-- Prove2me | Theorems.Thm_PI_LocalEndW_le_one_of_pow_eq
-- name    : PI.LocalEndW.le_one_of_pow_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:34:51.744801+00:00
-- url     : https://prove2.me/theorems/7e516fae-0f08-5da4-b300-ba9d752d1cd4
-- title:
--   Local End W: le one of pow eq
-- statement:
--   The Local End W construction uses the le one of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L47-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L47-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WithZero
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocalEndW.le_one_of_pow_eq {N ℓ m : ℕ} (hm : 0 < m) (hmℓ : m < ℓ)
    (hN : Valued.v ((N : v.adicCompletion F)) = exp (-(m : ℤ)))
    {y z : v.adicCompletion F} (h : z ^ ℓ = 1 + N * y ^ ℓ) : Valued.v y ≤ 1 := by sorry
