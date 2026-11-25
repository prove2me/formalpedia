-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isAlgClosure_Kloc
-- name    : ReciprocityTheory.Neutral.Cmp.isAlgClosure_Kloc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:01.922867+00:00
-- url     : https://prove2.me/theorems/6bd337ba-8dd6-41e4-97b5-9f3b75fcd390
-- title:
--   Cmp: is Alg Closure Kloc
-- statement:
--   The Cmp construction uses the is Alg Closure Kloc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L187-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/MemRangeOfAevalRatEqZero.lean#L187-L188

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

theorem ReciprocityTheory.Neutral.Cmp.isAlgClosure_Kloc (ι : Ω →+* PadicAlgCl p) : IsAlgClosure (Kloc F ι) (PadicAlgCl p) := by sorry
