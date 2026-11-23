-- Prove2me | Theorems.Thm_PI_Dv_Tr_phiS_apply
-- name    : PI.Dv.Tr.phiS_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:44.113387+00:00
-- url     : https://prove2.me/theorems/429c2584-d825-45c9-bc9c-a3866384f4e2
-- title:
--   Tr: phi S apply
-- statement:
--   The Tr construction uses the phi S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L24-L26

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

theorem PI.Dv.Tr.phiS_apply (T : GoodSet K G) (s : T.S) (X : Module.End K (T.W s)) :
    phiS T s X = ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x := by sorry
