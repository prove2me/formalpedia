-- Prove2me | Theorems.Thm_PI_Dv_Tr_mul_eS
-- name    : PI.Dv.Tr.mul_eS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:46.847714+00:00
-- url     : https://prove2.me/theorems/d486a7ff-e2b9-4560-ae95-3191813f4572
-- title:
--   Tr: mul e S
-- statement:
--   The Tr construction uses the mul e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L50-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
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
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.Tr.mul_eS (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    a * eS T s = phiS T s ((T.tau s).asAlgebraHom a) := by sorry
