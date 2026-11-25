-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_split_integral
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_integral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:19.49496+00:00
-- url     : https://prove2.me/theorems/eb52b85c-a592-4b5a-a1cb-72a1e51bca17
-- title:
--   Semi Deg Idx: split integral
-- statement:
--   The Semi Deg Idx construction uses the split integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L52-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L52-L82

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_integral {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hin : ∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) (hint : IsIntegralOn S X)
    (s t : Fin k → K) (hs : ∀ i, S.c (s i) ∈ C i) (ht : ∀ i, t i ∈ C i) :
    (∏ i, s i) * S.G.det * (∏ i, t i) ∈ (1 : Submodule (𝓞 K) K) := by sorry
