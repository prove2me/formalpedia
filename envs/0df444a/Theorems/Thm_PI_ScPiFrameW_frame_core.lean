-- Prove2me | Theorems.Thm_PI_ScPiFrameW_frame_core
-- name    : PI.ScPiFrameW.frame_core
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:32.940892+00:00
-- url     : https://prove2.me/theorems/225957b8-d7df-5a0f-a6cd-564644b02d8a
-- title:
--   Sc Pi Frame W: frame core
-- statement:
--   The Sc Pi Frame W construction uses the frame core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameCore.lean#L67-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameCore.lean#L67-L85

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

theorem PI.ScPiFrameW.frame_core (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by sorry
