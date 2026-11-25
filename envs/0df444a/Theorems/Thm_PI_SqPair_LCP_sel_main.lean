-- Prove2me | Theorems.Thm_PI_SqPair_LCP_sel_main
-- name    : PI.SqPair.LCP.sel_main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:46.449859+00:00
-- url     : https://prove2.me/theorems/bbcf1860-6b91-4513-b769-4a755ec9ed56
-- title:
--   LCP: sel main
-- statement:
--   The LCP construction uses the sel main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelMain.lean#L11-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelMain.lean#L11-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]

theorem PI.SqPair.LCP.sel_main (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h : Matrix ι ι R) (hA : IsUnit A.det) (hA' : IsUnit A'.det) (k : ℕ)
    (hrel : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A') :
    ∃ (m : ℕ) (h₁ : Matrix ι ι R), h = ϖ ^ m • h₁ ∧ m ≤ k ∧
      (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' ∧
      ((m = k ∧ IsUnit h₁.det) ∨
       (m < k ∧ ∃ (g₁ : Matrix ι ι R) (j : ι) (y : ι → R),
          g₁ * h₁ = ϖ ^ (2 * (k - m)) • 1 ∧ h₁ * g₁ = ϖ ^ (2 * (k - m)) • 1 ∧
          (∃ i, IsUnit ((h₁ *ᵥ Pi.single j 1) i)) ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ y) = 1 ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ (h₁ *ᵥ Pi.single j 1)) =
            ϖ ^ (2 * (k - m)) * A' j j ∧
          ϖ ^ (2 * (k - m)) • y = h₁ *ᵥ (g₁ *ᵥ y))) := by sorry
