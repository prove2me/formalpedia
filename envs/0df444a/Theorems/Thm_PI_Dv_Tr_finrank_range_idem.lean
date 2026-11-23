-- Prove2me | Theorems.Thm_PI_Dv_Tr_finrank_range_idem
-- name    : PI.Dv.Tr.finrank_range_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:27.858051+00:00
-- url     : https://prove2.me/theorems/b5409137-8ad3-4721-919f-f9f2829549dd
-- title:
--   Tr: finrank range idem
-- statement:
--   The Tr construction uses the finrank range idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L68-L70

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
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem PI.Dv.Tr.finrank_range_idem (f : Module.End K V) (h : f * f = f) :
    ((finrank K (LinearMap.range f) : ℕ) : K) = LinearMap.trace K V f := by sorry
