-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_denseRange
-- name    : ReciprocityTheory.Neutral.Cmp.denseRange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:07.886055+00:00
-- url     : https://prove2.me/theorems/17d6dcc3-6a20-4217-853d-e986306b3c58
-- title:
--   Cmp: dense Range
-- statement:
--   The Cmp construction uses the dense Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L193-L195

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
variable (F)
include F

theorem ReciprocityTheory.Neutral.Cmp.denseRange (ι : Ω →+* PadicAlgCl p) : DenseRange ι := by sorry
