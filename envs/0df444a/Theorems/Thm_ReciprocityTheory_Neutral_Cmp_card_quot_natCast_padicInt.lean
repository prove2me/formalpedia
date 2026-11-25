-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_card_quot_natCast_padicInt
-- name    : ReciprocityTheory.Neutral.Cmp.card_quot_natCast_padicInt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:12.69181+00:00
-- url     : https://prove2.me/theorems/5a294c76-cafc-4479-afdc-5d1f7d88f829
-- title:
--   Cmp: card quot nat Cast padic Int
-- statement:
--   The Cmp construction uses the card quot nat Cast padic Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L10-L37

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

theorem ReciprocityTheory.Neutral.Cmp.card_quot_natCast_padicInt (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(n : ℤ_[p])}) = p ^ padicValNat p n := by sorry
