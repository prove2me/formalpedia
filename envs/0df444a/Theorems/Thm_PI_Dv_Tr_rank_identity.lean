-- Prove2me | Theorems.Thm_PI_Dv_Tr_rank_identity
-- name    : PI.Dv.Tr.rank_identity
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:16.244932+00:00
-- url     : https://prove2.me/theorems/35f6c615-f9e3-47ec-91c4-f7f6a90baf1d
-- title:
--   Tr: rank identity
-- statement:
--   The Tr construction uses the rank identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L78-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean#L78-L99

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

theorem PI.Dv.Tr.rank_identity (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V) :
    finrank K (LinearMap.range (ρ.asAlgebraHom (eps P * eG T))) =
      ∑ s, nS T P s * finrank K (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) := by sorry
