-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_relIndex_span_ne_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.relIndex_span_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:45.506802+00:00
-- url     : https://prove2.me/theorems/2390bdeb-a296-4649-bde0-a71973481566
-- title:
--   Multiplicative Heights: rel Index span ne zero
-- statement:
--   The Multiplicative Heights construction uses the rel Index span ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBB.lean#L106-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBB.lean#L106-L151

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

theorem ReciprocityTheory.MultiplicativeHeights.relIndex_span_ne_zero {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (B : Submodule (𝓞 K) (Fin r → K))
    (hbB : ∀ i, b i ∈ B) (D : 𝓞 K) (hD : D ≠ 0)
    (hDB : ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by sorry
