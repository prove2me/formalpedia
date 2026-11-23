-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_combMap_injective
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.combMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:39.372953+00:00
-- url     : https://prove2.me/theorems/17b807e3-95dd-4140-9dfa-0b69bcfbb93e
-- title:
--   Semi Deg Idx: comb Map injective
-- statement:
--   The Semi Deg Idx construction uses the comb Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L56-L60

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.combMap_injective {K : Type} [Field K] {r k : ℕ} {b : Fin k → Fin r → K}
    (hb : LinearIndependent K b) : Function.Injective (combMap b) := by sorry
