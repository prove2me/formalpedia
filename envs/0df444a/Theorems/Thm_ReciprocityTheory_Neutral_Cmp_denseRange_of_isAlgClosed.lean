-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_denseRange_of_isAlgClosed
-- name    : ReciprocityTheory.Neutral.Cmp.denseRange_of_isAlgClosed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:39.698109+00:00
-- url     : https://prove2.me/theorems/b14d3086-6cdb-5fb6-9cb9-0a445786486c
-- title:
--   Cmp: dense Range of is Alg Closed
-- statement:
--   The Cmp construction uses the dense Range of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L81-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L81-L169

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
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
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.Neutral.Cmp.denseRange_of_isAlgClosed (ι : Ω →+* PadicAlgCl p) [IsAlgClosed Ω] : DenseRange ι := by sorry
