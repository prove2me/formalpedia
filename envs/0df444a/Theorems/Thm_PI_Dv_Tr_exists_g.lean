-- Prove2me | Theorems.Thm_PI_Dv_Tr_exists_g
-- name    : PI.Dv.Tr.exists_g
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:33:59.384919+00:00
-- url     : https://prove2.me/theorems/8771a0dc-305e-4cff-9ddf-b7eed2a8aa93
-- title:
--   Tr: exists g
-- statement:
--   The Tr construction uses the exists g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L84-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L84-L105

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

theorem PI.Dv.Tr.exists_g (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : V) (hx : x ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T)))
    (hx0 : x ≠ 0) : ∃ g, ρ.asAlgebraHom (eps P0) (ρ g x) ≠ 0 := by sorry
