-- Prove2me | Theorems.Thm_PI_Dv_Tr_eps_eq
-- name    : PI.Dv.Tr.eps_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:26.24704+00:00
-- url     : https://prove2.me/theorems/a135fc41-f52a-41cc-bd2d-068d7acb1072
-- title:
--   Tr: eps eq
-- statement:
--   The Tr construction uses the eps eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L23-L33

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
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical

theorem PI.Dv.Tr.eps_eq (P : Pair K G) : eps P = ((Fintype.card P.H : ℕ) : K)⁻¹ • epsSum P := by sorry
