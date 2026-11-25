-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_valuation_intCast_lt_one_iff
-- name    : ReciprocityTheory.Neutral.Cmp.valuation_intCast_lt_one_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:08.417065+00:00
-- url     : https://prove2.me/theorems/72362701-dae4-575f-ae1b-e5b3a20ef552
-- title:
--   Cmp: valuation int Cast lt one iff
-- statement:
--   The Cmp construction uses the valuation int Cast lt one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ValuationIntCastLtOneIff.lean#L28-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ValuationIntCastLtOneIff.lean#L28-L50

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

theorem ReciprocityTheory.Neutral.Cmp.valuation_intCast_lt_one_iff [CharZero Ω] (B : ValuationSubring Ω) (hp : B.valuation (p : Ω) < 1) (n : ℤ) :
    B.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by sorry
