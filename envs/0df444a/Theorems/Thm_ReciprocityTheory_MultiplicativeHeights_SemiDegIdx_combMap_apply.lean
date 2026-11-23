-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_combMap_apply
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.combMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:33.318857+00:00
-- url     : https://prove2.me/theorems/000c576d-5bae-4f5c-9347-0a8c3da0c4bf
-- title:
--   Semi Deg Idx: comb Map apply
-- statement:
--   The Semi Deg Idx construction uses the comb Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L39-L40

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
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
open NumberField Matrix
open scoped nonZeroDivisors

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.combMap_apply {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    combMap b t = ∑ i, t i • b i := by sorry
