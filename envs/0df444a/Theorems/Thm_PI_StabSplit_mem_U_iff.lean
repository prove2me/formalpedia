-- Prove2me | Theorems.Thm_PI_StabSplit_mem_U_iff
-- name    : PI.StabSplit.mem_U_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:21.811553+00:00
-- url     : https://prove2.me/theorems/a6238d54-bddb-510d-9f8e-ca076eead245
-- title:
--   Stab Split: mem U iff
-- statement:
--   The Stab Split construction uses the mem U iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/MulVecColOfMul.lean#L38-L42

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

theorem PI.StabSplit.mem_U_iff (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v) :
    v ∈ Uperp k r z z' γ ↔ ((Ym k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by sorry
