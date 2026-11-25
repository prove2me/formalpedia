-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_polyInner_eq_inner
-- name    : ReciprocityTheory.MultiplicativeHeights.polyInner_eq_inner
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:35.316386+00:00
-- url     : https://prove2.me/theorems/170fe836-393e-4bf4-8ecd-5f5f54328df5
-- title:
--   Multiplicative Heights: poly Inner eq inner
-- statement:
--   The Multiplicative Heights construction uses the poly Inner eq inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L65-L71

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset

theorem ReciprocityTheory.MultiplicativeHeights.polyInner_eq_inner {ι : Type*} (T : Finset (ι →₀ ℕ)) (P Q : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : polyInner P Q = inner ℂ (coeffVec T Q) (coeffVec T P) := by sorry
