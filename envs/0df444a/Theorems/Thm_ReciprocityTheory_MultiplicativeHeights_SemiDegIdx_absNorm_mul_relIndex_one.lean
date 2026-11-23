-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_absNorm_mul_relIndex_one
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:16.058207+00:00
-- url     : https://prove2.me/theorems/95b45f37-ad1a-4d6b-969c-ae017dc1707d
-- title:
--   Semi Deg Idx: abs Norm mul rel Index one
-- statement:
--   The Semi Deg Idx construction uses the abs Norm mul rel Index one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCA.lean#L78-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCA.lean#L78-L162

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one {K : Type} [Field K] [NumberField K] (C : Submodule (𝓞 K) K)
    (hC : C.FG) (h1 : 1 ≤ C) :
    FractionalIdeal.absNorm
        (⟨C, FractionalIdeal.isFractional_of_fg hC⟩ : FractionalIdeal (𝓞 K)⁰ K) *
      ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup : ℚ) = 1 := by sorry
