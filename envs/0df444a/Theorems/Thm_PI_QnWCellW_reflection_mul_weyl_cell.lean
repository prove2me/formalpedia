-- Prove2me | Theorems.Thm_PI_QnWCellW_reflection_mul_weyl_cell
-- name    : PI.QnWCellW.reflection_mul_weyl_cell
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:19:51.955494+00:00
-- url     : https://prove2.me/theorems/45aaca11-c70e-5de4-9e3d-3ecb6909cf7b
-- title:
--   Qn WCell W: reflection mul weyl cell
-- statement:
--   The Qn WCell W construction uses the reflection mul weyl cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L90-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L90-L109

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
set_option maxHeartbeats 800000

theorem PI.QnWCellW.reflection_mul_weyl_cell (k r : ℕ) (S : Finset ℕ) (c : Fin r → ℂ) (a : Fin r) (ha : a.val ∉ S) :
    w1 k r a (c a) * Wm k r S c = Wm k r (insert a.val S) c := by sorry
