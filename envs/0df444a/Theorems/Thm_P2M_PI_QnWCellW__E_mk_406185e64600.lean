-- Prove2me | Theorems.Thm_P2M_PI_QnWCellW__E_mk_406185e64600
-- name    : P2M_PI_QnWCellW__E_mk_406185e64600
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:58:39.904932+00:00
-- url     : https://prove2.me/theorems/a767a103-9313-40a8-bb5e-984dab5be8da
-- title:
--   P2 M PI Qn WCell W  E mk 406185e64600: P2 M PI Qn WCell W  E mk 406185e64600
-- statement:
--   The P2 M PI Qn WCell W  E mk 406185e64600 construction uses the P2 M PI Qn WCell W  E mk 406185e64600 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L171-L174

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

theorem P2M_PI_QnWCellW__E_mk_406185e64600 {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : ℕ) (hi : i < k + 1) (hj : j < k + 1) :
    μ ⟨i, hi⟩ ⟨j, hj⟩ = μE μ i j := by sorry

alias «PI».«QnWCellW».«μE_mk» := P2M_PI_QnWCellW__E_mk_406185e64600
