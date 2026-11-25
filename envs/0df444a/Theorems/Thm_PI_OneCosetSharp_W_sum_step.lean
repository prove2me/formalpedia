-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_sum_step
-- name    : PI.OneCosetSharp.W.sum_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:15.878849+00:00
-- url     : https://prove2.me/theorems/26930175-cead-5ebe-8957-381a8e73149b
-- title:
--   W: sum step
-- statement:
--   The W construction uses the sum step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/Assemble.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/Assemble.lean#L35-L43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE

theorem PI.OneCosetSharp.W.sum_step {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ)
    (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (hE : E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) :
    ∃ tt, PhiS ψ₀ χ k₀ m t j n' c n (h.symm.toLinearMap ∘ₗ xx1 xj tt) ≠ 0 := by sorry
