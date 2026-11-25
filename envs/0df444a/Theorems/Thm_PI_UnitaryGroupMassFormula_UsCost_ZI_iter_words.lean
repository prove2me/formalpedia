-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_iter_words
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.iter_words
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:58.555435+00:00
-- url     : https://prove2.me/theorems/64026015-4307-47c1-bef1-72d24c719a2a
-- title:
--   ZI: iter words
-- statement:
--   The ZI construction uses the iter words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterA.lean#L104-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterA.lean#L104-L235

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.iter_words (q : ℕ) (Kc : ℝ) (hKc : 0 ≤ Kc) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {α E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Cls : ℕ → (α → E) → Prop)
      (Dop : I → (α → E) → (α → E)) (Γ : V → α) (U : Set V) (c : I → V → (V →L[ℝ] ℝ)) (z₀ : V)
      (M lam : ℝ),
      IsOpen U → z₀ ∈ U → 1 ≤ M → 1 ≤ lam →
      (∀ b H, Cls (b + 1) H → Cls b H) →
      (∀ b H i, Cls (b + 1) H → Cls b (Dop i H)) →
      (∀ b H, Cls b H → ∀ z ∈ U, ContDiffAt ℝ b (fun z => H (Γ z)) z) →
      (∀ b H, Cls (b + 1) H → ∀ z ∈ U,
        fderiv ℝ (fun z => H (Γ z)) z = ∑ i, (c i z).smulRight (Dop i H (Γ z))) →
      (∀ i (n : ℕ), ContDiffOn ℝ n (c i) U) →
      (∀ i, ∀ a ≤ q, ‖iteratedFDeriv ℝ a (c i) z₀‖ ≤ Kc * M ^ (a + 1)) →
      ∀ b ≤ q, ∀ (H : α → E) (β : ℝ), Cls b H →
        (∀ w : List I, w.length ≤ b → ‖w.foldr Dop H (Γ z₀)‖ ≤ β * lam ^ w.length) →
        ‖iteratedFDeriv ℝ b (fun z => H (Γ z)) z₀‖ ≤ C * β * (lam * M) ^ b := by sorry
