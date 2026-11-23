-- Prove2me | Theorems.Thm_PI_Dv_Tr_key_scalar
-- name    : PI.Dv.Tr.key_scalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:50.710029+00:00
-- url     : https://prove2.me/theorems/f60f135f-69d9-4bee-bcc9-b46f1c396978
-- title:
--   Tr: key scalar
-- statement:
--   The Tr construction uses the key scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/MemRangeIdem.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/MemRangeIdem.lean#L36-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_MemRangeIdem
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
variable (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (cB : MonoidAlgebra K G → K)
  (g h : Fin (nS T P s) → G)
  (hlift : ∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s))
  {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
include hlift

theorem PI.Dv.Tr.key_scalar (a : MonoidAlgebra K G) (y : V) (hy : y ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) :
    ρ.asAlgebraHom (eps P0 * a) y = cB a • y := by sorry
