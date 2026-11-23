-- Prove2me | Theorems.Thm_PI_Dv_Tr_trace_mul_eS
-- name    : PI.Dv.Tr.trace_mul_eS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:54.116796+00:00
-- url     : https://prove2.me/theorems/929881ff-250c-4e98-9128-49079439652f
-- title:
--   Tr: trace mul e S
-- statement:
--   The Tr construction uses the trace mul e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L202-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L202-L228

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

theorem PI.Dv.Tr.trace_mul_eS (T : GoodSet K G) (s : T.S) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    ∃ c : K, ∀ a : MonoidAlgebra K G,
      LinearMap.trace K V (ρ.asAlgebraHom (a * eS T s)) = c * LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom a) := by sorry
