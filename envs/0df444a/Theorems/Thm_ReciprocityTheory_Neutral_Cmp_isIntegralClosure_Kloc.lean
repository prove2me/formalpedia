-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isIntegralClosure_Kloc
-- name    : ReciprocityTheory.Neutral.Cmp.isIntegralClosure_Kloc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:36.279733+00:00
-- url     : https://prove2.me/theorems/09c9bb10-ba84-4127-9cbd-fc75e3af5659
-- title:
--   Cmp: is Integral Closure Kloc
-- statement:
--   The Cmp construction uses the is Integral Closure Kloc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L114-L119

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
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
attribute [local instance] zpAlgInteger

theorem ReciprocityTheory.Neutral.Cmp.isIntegralClosure_Kloc (ι : Ω →+* PadicAlgCl p) :
    IsIntegralClosure 𝒪[Kloc F ι] ℤ_[p] (Kloc F ι) := by sorry
