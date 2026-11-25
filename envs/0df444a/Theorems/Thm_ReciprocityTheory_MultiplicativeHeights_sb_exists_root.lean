-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_exists_root
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_exists_root
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:23.921475+00:00
-- url     : https://prove2.me/theorems/6db46e53-f333-5cf8-b828-158763e74cff
-- title:
--   Multiplicative Heights: sb exists root
-- statement:
--   The Multiplicative Heights construction uses the sb exists root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L23-L35

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.MultiplicativeHeights.sb_exists_root {r : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ ∀ u, hq H u = normSq (Q *ᵥ u) := by sorry
