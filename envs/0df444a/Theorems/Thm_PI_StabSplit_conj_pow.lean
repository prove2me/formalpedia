-- Prove2me | Theorems.Thm_PI_StabSplit_conj_pow
-- name    : PI.StabSplit.conj_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:08.052524+00:00
-- url     : https://prove2.me/theorems/ec8e8753-b563-4f2f-86a5-0ffe7b2e5327
-- title:
--   Stab Split: conj pow
-- statement:
--   The Stab Split construction uses the conj pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L120-L126

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

theorem PI.StabSplit.conj_pow {N : ℕ} (A G Gi : Matrix (Fin N) (Fin N) ℂ) (h1 : Gi * G = 1) (h2 : G * Gi = 1) :
    ∀ p : ℕ, (Gi * A * G) ^ p = Gi * A ^ p * G
  := by sorry
