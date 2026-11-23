-- Prove2me | Theorems.Thm_UpperTheory_Top_PairGood_mono
-- name    : UpperTheory.Top.PairGood.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:42.357254+00:00
-- url     : https://prove2.me/theorems/5afeee72-ef66-4255-a368-e92fbef00502
-- title:
--   Pair Good: mono
-- statement:
--   The Pair Good construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean#L41-L42

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_PairGood
import Theorems.Thm_UpperTheory_Top_VVle_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.Top
open Formalism.HC

theorem UpperTheory.Top.PairGood.mono {M : ℕ} {eps Y X X' : ℝ} {q d : ℕ} (h : PairGood M eps Y X q d) (hX : X' ≤ X) : PairGood M eps Y X' q d := by sorry
