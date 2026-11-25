-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_integrable_mono_term
-- name    : ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.integrable_mono_term
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:02:51.268904+00:00
-- url     : https://prove2.me/theorems/75ca3e36-b000-47b4-a91b-e149ce451bd9
-- title:
--   Torus Lex Order: integrable mono term
-- statement:
--   The Torus Lex Order construction uses the integrable mono term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexC.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexC.lean#L29-L33

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate

theorem ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.integrable_mono_term {ι : Type} [Fintype ι] (t s : ι →₀ ℕ) :
    Integrable (fun θ => torusMono θ t * conj (torusMono θ s)) (torusProb ι) := by sorry
