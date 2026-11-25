-- Prove2me | Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_Q_perp_idem
-- name    : PI.UnitaryDimensionFormula.FrameAlg.Q_perp_idem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:37:45.52189+00:00
-- url     : https://prove2.me/theorems/d2b0e92b-4a7b-4d0c-bee2-bd96813b909a
-- title:
--   Frame Alg: Q perp idem
-- statement:
--   The Frame Alg construction uses the Q perp idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L100-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L100-L122

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI PI.UnitaryDimensionFormula PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
variable {r : ℕ}

theorem PI.UnitaryDimensionFormula.FrameAlg.Q_perp_idem (hJ : Formalism.UG.cT σ J = J) (hσ : ∀ a, σ (σ a) = a) {e f : Fin r → n → A} {z : n → A} (E₁ : A)
    (hE : E₁ * E₁ = E₁) (hEs : σ E₁ = E₁) (he : ∀ a, e a = E₁ • e a) (hf : ∀ a, f a = E₁ • f a)
    (hee : ∀ a b, Formalism.UG.hform σ J (e a) (e b) = 0) (hff : ∀ a b, Formalism.UG.hform σ J (f a) (f b) = 0)
    (hef : ∀ a b, Formalism.UG.hform σ J (e a) (f b) = if a = b then E₁ else 0)
    (hez : ∀ a, Formalism.UG.hform σ J (e a) z = 0) (hfz : ∀ a, Formalism.UG.hform σ J (f a) z = 0) (y : n → A) :
    (∀ b, Formalism.UG.hform σ J (e b) (Q σ J e f z y) = 0) ∧ (∀ b, Formalism.UG.hform σ J (f b) (Q σ J e f z y) = 0) ∧
      Formalism.UG.hform σ J z (Q σ J e f z y) = 0 := by sorry
