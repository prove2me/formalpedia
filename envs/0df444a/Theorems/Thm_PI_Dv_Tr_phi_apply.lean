-- Prove2me | Theorems.Thm_PI_Dv_Tr_phi_apply
-- name    : PI.Dv.Tr.phi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:10.065049+00:00
-- url     : https://prove2.me/theorems/defaab73-552f-4161-b41c-cf2d80f9c88e
-- title:
--   Tr: phi apply
-- statement:
--   The Tr construction uses the phi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L108-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L108-L113

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
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
open PI.Dv Module NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical

theorem PI.Dv.Tr.phi_apply {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) (P0 : Pair K G) (g : G)
    (y : V) :
    ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G g) y =
      ∑ h : P0.H, (((P0.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y) := by sorry
