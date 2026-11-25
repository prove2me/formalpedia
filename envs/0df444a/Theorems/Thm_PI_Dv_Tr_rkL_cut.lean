-- Prove2me | Theorems.Thm_PI_Dv_Tr_rkL_cut
-- name    : PI.Dv.Tr.rkL_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:49.242104+00:00
-- url     : https://prove2.me/theorems/5f2784bb-9c1d-40b7-9d8f-afa54303598b
-- title:
--   Tr: rk L cut
-- statement:
--   The Tr construction uses the rk L cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L135-L138

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
open NumberField
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.Tr.rkL_cut (A : Formalism.BasicNotions.HLat K) (hA : A.Good) (ρ : Representation K G A.V) (a : MonoidAlgebra K G) :
    rkL A (cut A ρ a A.L) = finrank K (LinearMap.range (ρ.asAlgebraHom a)) := by sorry
