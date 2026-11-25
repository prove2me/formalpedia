-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_index
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_index
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:07.296479+00:00
-- url     : https://prove2.me/theorems/c75b800c-1af8-50f4-8b7f-994cd187d8a6
-- title:
--   Multiplicative Heights: sdd index
-- statement:
--   The Multiplicative Heights construction uses the sdd index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean#L123-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean#L123-L158

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
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
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}

theorem ReciprocityTheory.MultiplicativeHeights.sdd_index {k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (c b₁ : Fin k₁ → Fin r → K) (hsat : satSub B b₀ = B ⊓ cutSub K r e) (hcB : ∀ j, c j ∈ B)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) :
    (satSub B b₀ ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex B.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b₁)).toAddSubgroup.relIndex
        (B.map (projGe K r e)).toAddSubgroup := by sorry
