-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_reps_meanZero
-- name    : ReciprocityTheory.Cheb.exists_reps_meanZero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:05.086959+00:00
-- url     : https://prove2.me/theorems/c7f85191-1e24-5955-8f6c-362087573647
-- title:
--   Cheb: exists reps mean Zero
-- statement:
--   The Cheb construction uses the exists reps mean Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/MeanZero.lean#L72-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/MeanZero.lean#L72-L185

import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormCongr
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.exists_reps_meanZero {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    latOf (mbc l b.1 c.1) ≤ latOf b.1 ∧
    ∃ reps : Finset (mixedSpace E), (∀ β ∈ reps, β ∈ latOf b.1) ∧
      (∀ α ∈ latOf b.1, ∃ l' ∈ latOf (mbc l b.1 c.1), ∃ β ∈ reps, α = l' + β) ∧
      (∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ latOf (mbc l b.1 c.1) → β₁ = β₂) ∧
      (∀ l' ∈ latOf (mbc l b.1 c.1), ∀ β ∈ reps, cfun χ b.1 c.1 (l' + β) = cfun χ b.1 c.1 β) ∧
      ∑ β ∈ reps, cfun χ b.1 c.1 β = 0 := by sorry
