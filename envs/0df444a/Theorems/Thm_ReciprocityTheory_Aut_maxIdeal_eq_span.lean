-- Prove2me | Theorems.Thm_ReciprocityTheory_Aut_maxIdeal_eq_span
-- name    : ReciprocityTheory.Aut.maxIdeal_eq_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:25.965928+00:00
-- url     : https://prove2.me/theorems/7d997f3c-df1d-57d3-b2ea-ec8b18369b67
-- title:
--   Aut: max Ideal eq span
-- statement:
--   The Aut construction uses the max Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/InstMainA.lean#L39-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/InstMainA.lean#L39-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ReciprocityTheory.Aut.maxIdeal_eq_span {π : v.adicCompletionIntegers F}
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π} := by sorry
