-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_intVec
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.mem_intVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:59.428138+00:00
-- url     : https://prove2.me/theorems/9825975e-36a2-4a23-b04d-73c0bbd3fe47
-- title:
--   Semi Deg Idx: mem int Vec
-- statement:
--   The Semi Deg Idx construction uses the mem int Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCA.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCA.lean#L37-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField
open scoped nonZeroDivisors

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.mem_intVec {K : Type} [Field K] [NumberField K] {k : ℕ} {x : Fin k → K} :
    x ∈ intVec K k ↔ ∀ i, x i ∈ (1 : Submodule (𝓞 K) K) := by sorry
