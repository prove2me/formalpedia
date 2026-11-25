-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_split_selfDual
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_selfDual
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:31.991275+00:00
-- url     : https://prove2.me/theorems/8cc0433d-7dcd-4030-a09f-cb198bbacdaf
-- title:
--   Semi Deg Idx: split self Dual
-- statement:
--   The Semi Deg Idx construction uses the split self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L84-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L84-L131

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_selfDual {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hdec : ∀ x ∈ X, ∃ t : Fin k → K, (∀ i, t i ∈ C i) ∧ x = ∑ i, t i • z i)
    (hsd : IsSelfDual S X) (hG : S.G.det ≠ 0) (u : Fin k → K)
    (hu : ∀ j, ∀ w, S.c w ∈ C j → u j * w ∈ (1 : Submodule (𝓞 K) K)) :
    ∏ j, u j ∈ Submodule.span (𝓞 K) {S.G.det} * ∏ i, C i := by sorry
