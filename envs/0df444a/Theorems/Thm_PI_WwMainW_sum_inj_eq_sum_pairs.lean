-- Prove2me | Theorems.Thm_PI_WwMainW_sum_inj_eq_sum_pairs
-- name    : PI.WwMainW.sum_inj_eq_sum_pairs
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:27.160284+00:00
-- url     : https://prove2.me/theorems/5ba5872f-426d-4f3d-ba72-a7f8dd65396c
-- title:
--   Ww Main W: sum inj eq sum pairs
-- statement:
--   The Ww Main W construction uses the sum inj eq sum pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/SumInjEqSumPairs.lean#L11-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/SumInjEqSumPairs.lean#L11-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_SumInjEqSumPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Equiv
noncomputable section
open PI PI.WwMainW

theorem PI.WwMainW.sum_inj_eq_sum_pairs {R : Type} [CommRing R] {p n : ℕ} (F : (Fin p → Fin n) → R) :
    ∑ x : (Fin p ↪o Fin n) × Perm (Fin p), F (x.1 ∘ x.2) =
      ∑ f ∈ univ.filter (fun f : Fin p → Fin n => Function.Injective f), F f := by sorry
