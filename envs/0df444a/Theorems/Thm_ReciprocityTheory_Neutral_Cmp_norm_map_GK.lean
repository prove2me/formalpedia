-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_map_GK
-- name    : ReciprocityTheory.Neutral.Cmp.norm_map_GK
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:02.004069+00:00
-- url     : https://prove2.me/theorems/c1b3b0e8-c37c-44ce-9219-2af10a235027
-- title:
--   Cmp: norm map GK
-- statement:
--   The Cmp construction uses the norm map GK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L224-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L224-L225

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

theorem ReciprocityTheory.Neutral.Cmp.norm_map_GK (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by sorry
