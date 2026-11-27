-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_exists_norm_sub_lt
-- name    : ReciprocityTheory.Neutral.Cmp.exists_norm_sub_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:37:18.368831+00:00
-- url     : https://prove2.me/theorems/72aaa200-1742-42e6-a182-5eb637b002bf
-- title:
--   Cmp: exists norm sub lt
-- statement:
--   The Cmp construction uses the exists norm sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L197-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L197-L219

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

theorem ReciprocityTheory.Neutral.Cmp.exists_norm_sub_lt (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : F, ‖(x : PadicAlgCl p) - ι (algebraMap F Ω y)‖ < ε := by sorry
