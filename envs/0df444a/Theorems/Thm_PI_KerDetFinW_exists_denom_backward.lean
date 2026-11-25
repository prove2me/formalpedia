-- Prove2me | Theorems.Thm_PI_KerDetFinW_exists_denom_backward
-- name    : PI.KerDetFinW.exists_denom_backward
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:33:33.475546+00:00
-- url     : https://prove2.me/theorems/a51eda34-4762-4bfc-8f13-6e98f0af47da
-- title:
--   Ker Det Fin W: exists denom backward
-- statement:
--   The Ker Det Fin W construction uses the exists denom backward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsDenomBackward.lean#L54-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsDenomBackward.lean#L54-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
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

theorem PI.KerDetFinW.exists_denom_backward {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : Fin 4 × n → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) → ∀ a,
      (N : E) * g₀.symm v a ∈ I := by sorry
