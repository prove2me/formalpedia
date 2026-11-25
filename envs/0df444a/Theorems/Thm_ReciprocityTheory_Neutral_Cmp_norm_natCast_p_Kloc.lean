-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_natCast_p_Kloc
-- name    : ReciprocityTheory.Neutral.Cmp.norm_natCast_p_Kloc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:44.139298+00:00
-- url     : https://prove2.me/theorems/b85a7cd7-99f7-4c5b-8bfd-f43357d97de2
-- title:
--   Cmp: norm nat Cast p Kloc
-- statement:
--   The Cmp construction uses the norm nat Cast p Kloc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelA.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelA.lean#L34-L38

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
attribute [local instance] locRel

theorem ReciprocityTheory.Neutral.Cmp.norm_natCast_p_Kloc (ι : Ω →+* PadicAlgCl p) : ‖(((p : ℕ) : Kloc F ι) : PadicAlgCl p)‖ < 1 := by sorry
