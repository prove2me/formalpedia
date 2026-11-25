-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_lies_over_ratPrime
-- name    : ReciprocityTheory.Neutral.Cmp.lies_over_ratPrime
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:37.175787+00:00
-- url     : https://prove2.me/theorems/c7004459-2dab-421b-999f-7320b7b594df
-- title:
--   Cmp: lies over rat Prime
-- statement:
--   The Cmp construction uses the lies over rat Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ValuationIntCastLtOneIff.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ValuationIntCastLtOneIff.lean#L65-L72

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.Neutral.Cmp.lies_over_ratPrime [CharZero Ω] (B : ValuationSubring Ω) (hp : B.valuation (p : Ω) < 1) (x : 𝓞 ℚ) :
    B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ (ratPrime p).asIdeal := by sorry
