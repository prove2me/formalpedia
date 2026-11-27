-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_card_quot_natCast_Kloc
-- name    : ReciprocityTheory.Neutral.Cmp.card_quot_natCast_Kloc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:32:11.585721+00:00
-- url     : https://prove2.me/theorems/8e095281-75c0-4e49-afb7-ec2a448a8455
-- title:
--   Cmp: card quot nat Cast Kloc
-- statement:
--   The Cmp construction uses the card quot nat Cast Kloc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L121-L133

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

theorem ReciprocityTheory.Neutral.Cmp.card_quot_natCast_Kloc (ι : Ω →+* PadicAlgCl p) {n : ℕ} (hn : n ≠ 0) :
    Nat.card (𝒪[Kloc F ι] ⧸ Ideal.span {(n : 𝒪[Kloc F ι])}) =
      p ^ (padicValNat p n * Module.finrank ℚ_[p] (Kloc F ι)) := by sorry
