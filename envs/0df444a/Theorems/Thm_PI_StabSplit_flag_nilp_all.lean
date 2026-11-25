-- Prove2me | Theorems.Thm_PI_StabSplit_flag_nilp_all
-- name    : PI.StabSplit.flag_nilp_all
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:36.555634+00:00
-- url     : https://prove2.me/theorems/c71887ac-7f4a-5742-82ea-6ec9173ac2cd
-- title:
--   Stab Split: flag nilp all
-- statement:
--   The Stab Split construction uses the flag nilp all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L113-L118

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_MulVecColOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.StabSplit

theorem PI.StabSplit.flag_nilp_all {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ m) *ᵥ v a = 0 := by sorry
