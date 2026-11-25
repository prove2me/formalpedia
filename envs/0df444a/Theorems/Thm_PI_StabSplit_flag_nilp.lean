-- Prove2me | Theorems.Thm_PI_StabSplit_flag_nilp
-- name    : PI.StabSplit.flag_nilp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:25.541793+00:00
-- url     : https://prove2.me/theorems/1889722f-4231-5d69-8af4-84078cadcd9d
-- title:
--   Stab Split: flag nilp
-- statement:
--   The Stab Split construction uses the flag nilp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L94-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L94-L111

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

theorem PI.StabSplit.flag_nilp {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ (a.val + 1)) *ᵥ v a = 0 := by sorry
