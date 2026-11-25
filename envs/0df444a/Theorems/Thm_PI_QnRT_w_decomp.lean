-- Prove2me | Theorems.Thm_PI_QnRT_w_decomp
-- name    : PI.QnRT.w_decomp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:36.763002+00:00
-- url     : https://prove2.me/theorems/37f98e87-279e-5ab4-8448-429ad7888d29
-- title:
--   Qn RT: w decomp
-- statement:
--   The Qn RT construction uses the w decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L193-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L193-L212

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}

theorem PI.QnRT.w_decomp (l : Fin r) (b : ℂ) :
    w1 k r l b = w1 k r l 0 + b • single (esI k r l) (eI k r l) 1 +
      (star b)⁻¹ • single (eI k r l) (esI k r l) 1 := by sorry
