-- Prove2me | Theorems.Thm_PI_KerDetFinW_int_mul_mem
-- name    : PI.KerDetFinW.int_mul_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:32:29.066108+00:00
-- url     : https://prove2.me/theorems/7a8c9a58-8cba-5238-8d03-f116631b7ea0
-- title:
--   Ker Det Fin W: int mul mem
-- statement:
--   The Ker Det Fin W construction uses the int mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L42-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
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

theorem PI.KerDetFinW.int_mul_mem {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {k : K} (hk : k ∈ (algebraMap (𝓞 K) K).range)
    {y : E} (hy : y ∈ I) : algebraMap K E k * y ∈ I := by sorry
