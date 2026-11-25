-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_map
-- name    : ReciprocityTheory.Neutral.Cmp.norm_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:46.922524+00:00
-- url     : https://prove2.me/theorems/3aa69cd8-eb58-5785-8270-1ae079921283
-- title:
--   Cmp: norm map
-- statement:
--   The Cmp construction uses the norm map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L221-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L221-L222

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

theorem ReciprocityTheory.Neutral.Cmp.norm_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by sorry
