-- Prove2me | Theorems.Thm_PI_OpWords_vanish_at
-- name    : PI.OpWords.vanish_at
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:55.745255+00:00
-- url     : https://prove2.me/theorems/75331b3d-71bf-48be-8a78-d65565575e3f
-- title:
--   Op Words: vanish at
-- statement:
--   The Op Words construction uses the vanish at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishMain.lean#L54-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishMain.lean#L54-L130

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem PI.OpWords.vanish_at {d c : ℕ} (W : Submodule K (Pol K k)) (hW : W ≤ Bihom K k d)
    (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) (hwt : ∀ f ∈ W, WtLe K k c f) (hcd : c < d)
    (i0 : Fin k) (S : Finset (Fin k)) :
    ∀ p : Fin k ⊕ Fin k → K, p (Sum.inl i0) ≠ 0 → (∀ b, b ≠ i0 → p (Sum.inl b) ≠ 0 → b ∈ S) →
      ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → ∀ g ∈ W, eval p g = 0 := by sorry
