-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_primesOverFinset_span_le_finrank
-- name    : ReciprocityTheory.Neutral.Bridge.card_primesOverFinset_span_le_finrank
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:05.787798+00:00
-- url     : https://prove2.me/theorems/cefda3cb-da20-5a84-ac6f-585223d18629
-- title:
--   Bridge: card primes Over Finset span le finrank
-- statement:
--   The Bridge construction uses the card primes Over Finset span le finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L90-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L90-L107

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]

theorem ReciprocityTheory.Neutral.Bridge.card_primesOverFinset_span_le_finrank (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)).card ≤ Module.finrank ℚ K := by sorry
