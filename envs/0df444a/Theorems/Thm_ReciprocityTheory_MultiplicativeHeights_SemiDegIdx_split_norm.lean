-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_split_norm
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:13.066316+00:00
-- url     : https://prove2.me/theorems/0a44b95b-69d3-4b8b-8f5c-8a8e3027884f
-- title:
--   Semi Deg Idx: split norm
-- statement:
--   The Semi Deg Idx construction uses the split norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCE.lean#L24-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCE.lean#L24-L88

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_norm {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (X : Submodule (𝓞 K) (Fin k → K)) (hfg : X.FG) (hstd : intVec K k ≤ X)
    (hint : IsIntegralOn S X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, J ≤ 1 ∧ (IsSelfDual S X → S.G.det ≠ 0 → 1 ≤ J) ∧
      FractionalIdeal.absNorm J * (vecIdx X : ℚ) ^ 2 = |Algebra.norm ℚ S.G.det| := by sorry
