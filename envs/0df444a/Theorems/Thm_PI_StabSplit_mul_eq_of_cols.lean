-- Prove2me | Theorems.Thm_PI_StabSplit_mul_eq_of_cols
-- name    : PI.StabSplit.mul_eq_of_cols
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:09.411935+00:00
-- url     : https://prove2.me/theorems/2dcd5d38-25fb-4186-83ce-1435de35f951
-- title:
--   Stab Split: mul eq of cols
-- statement:
--   The Stab Split construction uses the mul eq of cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L80-L85

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

theorem PI.StabSplit.mul_eq_of_cols {m : Type*} [Fintype m] (k r : ℕ) (A : B.Mat k r)
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : ∀ j, A *ᵥ (fun i => C i j) = fun i => C i j) :
    A * C = C := by sorry
