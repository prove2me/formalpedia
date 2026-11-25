-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_smul_mem_span
-- name    : ReciprocityTheory.MultiplicativeHeights.exists_smul_mem_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:15.47644+00:00
-- url     : https://prove2.me/theorems/bae5fa2f-4d37-5748-b9ed-239a939f17ce
-- title:
--   Multiplicative Heights: exists smul mem span
-- statement:
--   The Multiplicative Heights construction uses the exists smul mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBB.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBB.lean#L67-L80

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBB
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
open Matrix NumberField

theorem ReciprocityTheory.MultiplicativeHeights.exists_smul_mem_span {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (x : Fin r → K) (hx : x ∈ Submodule.span K (Set.range b)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b) := by sorry
