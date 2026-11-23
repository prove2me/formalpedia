-- Prove2me | Theorems.Thm_PI_Dv_Tr_mul_idem
-- name    : PI.Dv.Tr.mul_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:35.21634+00:00
-- url     : https://prove2.me/theorems/f529f3e3-d4fd-4b89-b563-a6f3504feae8
-- title:
--   Tr: mul idem
-- statement:
--   The Tr construction uses the mul idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L62-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module

theorem PI.Dv.Tr.mul_idem {R : Type*} [Semiring R] {a b : R} (ha : a * a = a) (hb : b * b = b) (hc : b * a = a * b) :
    (a * b) * (a * b) = a * b := by sorry
