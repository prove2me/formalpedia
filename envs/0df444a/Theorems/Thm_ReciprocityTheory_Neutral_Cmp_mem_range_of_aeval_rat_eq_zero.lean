-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_mem_range_of_aeval_rat_eq_zero
-- name    : ReciprocityTheory.Neutral.Cmp.mem_range_of_aeval_rat_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:21.61397+00:00
-- url     : https://prove2.me/theorems/3b2e6816-a09e-4e83-a484-806aba157947
-- title:
--   Cmp: mem range of aeval rat eq zero
-- statement:
--   The Cmp construction uses the mem range of aeval rat eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L11-L22

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

theorem ReciprocityTheory.Neutral.Cmp.mem_range_of_aeval_rat_eq_zero (ι : Ω →+* PadicAlgCl p) [IsAlgClosed Ω] {g : Polynomial ℚ} (hg : g ≠ 0)
    {b : PadicAlgCl p} (hb : Polynomial.aeval b g = 0) : b ∈ ι.range := by sorry
