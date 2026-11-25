-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isScalarTower_zp_Kloc_alg
-- name    : ReciprocityTheory.Neutral.Cmp.isScalarTower_zp_Kloc_alg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:00.920083+00:00
-- url     : https://prove2.me/theorems/2a2e60d9-cc52-4129-9bdc-7cc3e67c920e
-- title:
--   Cmp: is Scalar Tower zp Kloc alg
-- statement:
--   The Cmp construction uses the is Scalar Tower zp Kloc alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L98-L99

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

theorem ReciprocityTheory.Neutral.Cmp.isScalarTower_zp_Kloc_alg (ι : Ω →+* PadicAlgCl p) : IsScalarTower ℤ_[p] (Kloc F ι) (PadicAlgCl p) := by sorry
