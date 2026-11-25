-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isIntegral_zp_Kloc_iff
-- name    : ReciprocityTheory.Neutral.Cmp.isIntegral_zp_Kloc_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:18.395854+00:00
-- url     : https://prove2.me/theorems/da237a1d-2de4-4c8e-9c81-131664a07066
-- title:
--   Cmp: is Integral zp Kloc iff
-- statement:
--   The Cmp construction uses the is Integral zp Kloc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L108-L112

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

theorem ReciprocityTheory.Neutral.Cmp.isIntegral_zp_Kloc_iff (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) :
    IsIntegral ℤ_[p] x ↔ IsIntegral (PadicInt.subring p) (x : PadicAlgCl p) := by sorry
