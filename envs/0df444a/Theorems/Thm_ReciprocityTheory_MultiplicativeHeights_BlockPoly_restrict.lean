-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_BlockPoly_restrict
-- name    : ReciprocityTheory.MultiplicativeHeights.BlockPoly.restrict
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:34.175394+00:00
-- url     : https://prove2.me/theorems/8d8da4b0-a4f3-4e28-9a83-987568fe02db
-- title:
--   Block Poly: restrict
-- statement:
--   The Block Poly construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresB.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresB.lean#L16-L24

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB
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
open MeasureTheory Metric

theorem ReciprocityTheory.MultiplicativeHeights.BlockPoly.restrict {k n : ℕ} {a : Fin (k + 1) → ℕ} {F : (Fin (k + 1) → Fin n → ℂ) → ℂ}
    (hF : BlockPoly (k + 1) n a F) (v : Fin n → ℂ) :
    BlockPoly k n (fun j => a j.succ) (fun p => F (Fin.cons v p)) := by sorry
