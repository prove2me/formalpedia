-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_append_li
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_append_li
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:14.506999+00:00
-- url     : https://prove2.me/theorems/05678c54-0fdc-4df7-a001-3f15a97e37ab
-- title:
--   Multiplicative Heights: sdd append li
-- statement:
--   The Multiplicative Heights construction uses the sdd append li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean#L47-L64

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

theorem ReciprocityTheory.MultiplicativeHeights.sdd_append_li {k₀ k₁ : ℕ} (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    LinearIndependent K (Fin.append b₀ c) := by sorry
