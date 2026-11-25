-- Prove2me | Theorems.Thm_PI_ET_sum_comp_perm
-- name    : PI.ET.sum_comp_perm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:33.177963+00:00
-- url     : https://prove2.me/theorems/1e8680d6-3cf5-4c8f-a47a-d23d9d8e08ec
-- title:
--   ET: sum comp perm
-- statement:
--   The ET construction uses the sum comp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/ProdLeOfInjective.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/ProdLeOfInjective.lean#L21-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ProdLeOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ET

theorem PI.ET.sum_comp_perm {M : Type*} [AddCommMonoid M] {k n : ℕ} (F : (Fin k → Fin n) → M)
    (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → Fin n, F (fun i => f (τ i)) = ∑ f, F f := by sorry
