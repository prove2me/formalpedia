-- Prove2me | Theorems.Thm_PI_KerDetFinW_nat_mul_mem
-- name    : PI.KerDetFinW.nat_mul_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:00.819728+00:00
-- url     : https://prove2.me/theorems/ed34b214-2581-5b66-ab30-c43ce462f92d
-- title:
--   Ker Det Fin W: nat mul mem
-- statement:
--   The Ker Det Fin W construction uses the nat mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L54-L59

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

theorem PI.KerDetFinW.nat_mul_mem {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (c : ℕ) {y : E} (hy : y ∈ I) :
    (c : E) * y ∈ I := by sorry
