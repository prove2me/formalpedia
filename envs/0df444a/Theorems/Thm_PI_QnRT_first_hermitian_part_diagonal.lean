-- Prove2me | Theorems.Thm_PI_QnRT_first_hermitian_part_diagonal
-- name    : PI.QnRT.first_hermitian_part_diagonal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:40:40.437529+00:00
-- url     : https://prove2.me/theorems/aa85a053-3298-4db9-9066-a5b37f4a8c90
-- title:
--   Qn RT: first hermitian part diagonal
-- statement:
--   The Qn RT construction uses the first hermitian part diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L151-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L151-L170

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

theorem PI.QnRT.first_hermitian_part_diagonal (l : Fin r) : hpart1 (Hpk k r) (single (esI k r l) (esI k r l) 1) =
    dz l (-((1 / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) := by sorry
