-- Prove2me | Theorems.Thm_PI_ScPiFrameW_gs_step
-- name    : PI.ScPiFrameW.gs_step
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:32.214027+00:00
-- url     : https://prove2.me/theorems/afec437e-28ce-56da-96d9-26e1ebeb3ee6
-- title:
--   Sc Pi Frame W: gs step
-- statement:
--   The Sc Pi Frame W construction uses the gs step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameCore.lean#L16-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameCore.lean#L16-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_PosOfPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameCore
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
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}

theorem PI.ScPiFrameW.gs_step (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ))
    (m : ℕ) (hm : m < k) (w : Fin m → Fin n → ℂ)
    (hwo : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hwp : ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0) :
    ∃ w' : Fin (m + 1) → Fin n → ℂ, (∀ a b, hJ ε (w' a) (w' b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w' a) = 0 ∧ hJ ε (f c) (w' a) = 0) ∧ hJ ε z (w' a) = 0 := by sorry
