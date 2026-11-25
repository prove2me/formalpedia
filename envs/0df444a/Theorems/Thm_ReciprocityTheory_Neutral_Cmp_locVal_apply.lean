-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_locVal_apply
-- name    : ReciprocityTheory.Neutral.Cmp.locVal_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:41.444601+00:00
-- url     : https://prove2.me/theorems/627627a5-232b-4c1d-a97e-a8fe2e3ef575
-- title:
--   Cmp: loc Val apply
-- statement:
--   The Cmp construction uses the loc Val apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelA.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelA.lean#L14-L15

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
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
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.Neutral.Cmp.locVal_apply (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) : ((locVal ι x : NNReal) : ℝ) = ‖(x : PadicAlgCl p)‖ := by sorry
