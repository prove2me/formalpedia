-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_card_quot_span_algebraMap
-- name    : ReciprocityTheory.Neutral.Cmp.card_quot_span_algebraMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:12.218703+00:00
-- url     : https://prove2.me/theorems/8d6ac57e-c3c3-4fc4-8e4f-84cc57d32288
-- title:
--   Cmp: card quot span algebra Map
-- statement:
--   The Cmp construction uses the card quot span algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L39-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean#L39-L75

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

theorem ReciprocityTheory.Neutral.Cmp.card_quot_span_algebraMap {R C ι : Type*} [CommRing R] [CommRing C] [Algebra R C] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι R C) (r : R) :
    Nat.card (C ⧸ Ideal.span {algebraMap R C r}) = Nat.card (R ⧸ Ideal.span {r}) ^ Fintype.card ι := by sorry
