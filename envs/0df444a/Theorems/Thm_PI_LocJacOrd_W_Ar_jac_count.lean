-- Prove2me | Theorems.Thm_PI_LocJacOrd_W_Ar_jac_count
-- name    : PI.LocJacOrd.W.Ar.jac_count
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:49.200124+00:00
-- url     : https://prove2.me/theorems/cb4bdc15-9460-5298-a2be-3da3f1c8a5ab
-- title:
--   Ar: jac count
-- statement:
--   The Ar construction uses the jac count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L74-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W PI.LocJacOrd.W.Ar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical

theorem PI.LocJacOrd.W.Ar.jac_count (r : ℕ) (b : Fin (r + 1) → ℝ) :
    ∏ l : Fin r, ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), b i =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then b p.1 else 1) := by sorry
