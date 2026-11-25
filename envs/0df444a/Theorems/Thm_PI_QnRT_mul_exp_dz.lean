-- Prove2me | Theorems.Thm_PI_QnRT_mul_exp_dz
-- name    : PI.QnRT.mul_exp_dz
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:00.037771+00:00
-- url     : https://prove2.me/theorems/f434a710-42a2-400b-ac99-ea2af46eee8e
-- title:
--   Qn RT: mul exp dz
-- statement:
--   The Qn RT construction uses the mul exp dz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L250-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L250-L263

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

theorem PI.QnRT.mul_exp_dz (l : Fin r) (a κ : ℂ) (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (t : ℝ) :
    w1 k r l a * g₁ * NormedSpace.exp ((t : ℂ) • dz l κ (-star κ)) =
      w1 k r l (a * Complex.exp (t * κ)) * g₁ := by sorry
