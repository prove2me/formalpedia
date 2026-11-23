-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coe_prod_frac
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coe_prod_frac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:27.791533+00:00
-- url     : https://prove2.me/theorems/8773944a-43a9-4861-803a-3910d40ccc91
-- title:
--   Semi Deg Idx: coe prod frac
-- statement:
--   The Semi Deg Idx construction uses the coe prod frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCE.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCE.lean#L16-L19

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coe_prod_frac {K : Type} [Field K] [NumberField K] {k : ℕ}
    (F : Fin k → FractionalIdeal (𝓞 K)⁰ K) :
    ((∏ i, F i : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = ∏ i, (F i : Submodule (𝓞 K) K) := by sorry
