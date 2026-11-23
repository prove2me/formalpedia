-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_prod_eq_span_prod
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.prod_eq_span_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:38.200802+00:00
-- url     : https://prove2.me/theorems/2f475418-df8e-47c3-8436-5ef6c7b18039
-- title:
--   Semi Deg Idx: prod eq span prod
-- statement:
--   The Semi Deg Idx construction uses the prod eq span prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCE.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCE.lean#L10-L14

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
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
open scoped nonZeroDivisors Pointwise

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.prod_eq_span_prod {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) :
    ∏ i, p i = Submodule.span (𝓞 K) (∏ i, (p i : Set K)) := by sorry
