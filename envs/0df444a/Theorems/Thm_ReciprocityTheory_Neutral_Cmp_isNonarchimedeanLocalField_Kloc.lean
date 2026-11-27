-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isNonarchimedeanLocalField_Kloc
-- name    : ReciprocityTheory.Neutral.Cmp.isNonarchimedeanLocalField_Kloc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:37:20.227322+00:00
-- url     : https://prove2.me/theorems/d0c420a1-d102-4f88-b458-cb97598efad9
-- title:
--   Cmp: is Nonarchimedean Local Field Kloc
-- statement:
--   The Cmp construction uses the is Nonarchimedean Local Field Kloc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelA.lean#L47-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelA.lean#L47-L89

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

theorem ReciprocityTheory.Neutral.Cmp.isNonarchimedeanLocalField_Kloc (ι : Ω →+* PadicAlgCl p) : IsNonarchimedeanLocalField (Kloc F ι) := by sorry
