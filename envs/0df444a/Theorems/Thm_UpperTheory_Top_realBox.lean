-- Prove2me | Theorems.Thm_UpperTheory_Top_realBox
-- name    : UpperTheory.Top.realBox
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:55.672281+00:00
-- url     : https://prove2.me/theorems/eefa7b8d-da67-577a-bd5f-cb96f54af952
-- title:
--   Top: real Box
-- statement:
--   The Top construction uses the real Box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/RealBox.lean#L99-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/RealBox.lean#L99-L112

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_RealSplit
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_RealBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC UpperTheory.Top

theorem UpperTheory.Top.realBox :
    ∀ (M : ℕ) (φ : Frame) (H : HostRaw φ) (eps Y X : ℝ), 0 < M → (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * M) → ordCompl[2] H.QS ∣ M →
      PairGood M eps Y X H.q H.d →
      (∀ χ : PChar, H.IsCharE χ.χ → χ.IsReal → (H.q ∣ χ.N ∨ H.d ∣ χ.N) →
        ZeroBox (height M eps Y (if H.d ∣ χ.N then 1 else 0)) χ.χ ∧
          (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y (if H.d ∣ χ.N then 1 else 0)) ∧ RealBox H := by sorry
