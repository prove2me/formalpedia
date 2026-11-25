-- Prove2me | Theorems.Thm_PI_LocJacOrd_W_Ar_arith_real
-- name    : PI.LocJacOrd.W.Ar.arith_real
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:23.252287+00:00
-- url     : https://prove2.me/theorems/f5aa1b28-d7f7-4764-832d-9c0fed150cdc
-- title:
--   Ar: arith real
-- statement:
--   The Ar construction uses the arith real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L89-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L89-L145

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

theorem PI.LocJacOrd.W.Ar.arith_real (r : ℕ) (m : ℝ) (a : Fin (r + 1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    m ^ ((r + 1) * (r + 1)) * (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((a i * a j) ^ 2)⁻¹) *
        ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
          a i ^ 2) ^ 2) ^ 2 =
      (∏ q : UIdx r, (m ^ 2 * (a q.1.1 / a q.1.2) ^ 4)) * ∏ l : Fin (r + 1), (m * (a l ^ 4)⁻¹) := by sorry
