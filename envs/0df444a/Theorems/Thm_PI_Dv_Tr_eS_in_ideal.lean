-- Prove2me | Theorems.Thm_PI_Dv_Tr_eS_in_ideal
-- name    : PI.Dv.Tr.eS_in_ideal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:56.664538+00:00
-- url     : https://prove2.me/theorems/29776954-1753-464c-88bd-0d574135b7a8
-- title:
--   Tr: e S in ideal
-- statement:
--   The Tr construction uses the e S in ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L60-L74

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

theorem PI.Dv.Tr.eS_in_ideal (T : GoodSet K G) (s : T.S) (P0 : Pair K G)
    (hY : (T.tau s).asAlgebraHom (eps P0) ≠ 0) :
    ∃ (n : ℕ) (a b : Fin n → MonoidAlgebra K G), ∑ i, a i * (eps P0 * (b i * eS T s)) = eS T s := by sorry
