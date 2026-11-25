-- Prove2me | Theorems.Thm_PI_KerDetFinW_exists_nat_mul_mem_frac
-- name    : PI.KerDetFinW.exists_nat_mul_mem_frac
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:01.154683+00:00
-- url     : https://prove2.me/theorems/fa9da4e4-f5d1-554e-bc40-7341c4387bb2
-- title:
--   Ker Det Fin W: exists nat mul mem frac
-- statement:
--   The Ker Det Fin W construction uses the exists nat mul mem frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L61-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L61-L72

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

theorem PI.KerDetFinW.exists_nat_mul_mem_frac {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (y : E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) * y ∈ I := by sorry
