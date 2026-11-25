-- Prove2me | Theorems.Thm_PI_Dv_Tr_vanish
-- name    : PI.Dv.Tr.vanish
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:38.234529+00:00
-- url     : https://prove2.me/theorems/ebafca9a-9701-48ed-ad75-93d690fa7924
-- title:
--   Tr: vanish
-- statement:
--   The Tr construction uses the vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L76-L82

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

theorem PI.Dv.Tr.vanish {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) (P0 : Pair K G) (x : V)
    (h : ∀ g, ρ.asAlgebraHom (eps P0) (ρ g x) = 0) (c : MonoidAlgebra K G) :
    ρ.asAlgebraHom (eps P0 * c) x = 0 := by sorry
