-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_H0_comp_equiv
-- name    : ReciprocityTheory.Neutral.Bridge.card_H0_comp_equiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:20.095776+00:00
-- url     : https://prove2.me/theorems/c0c24a1b-4fd6-4a60-b43e-071fa8ae27aa
-- title:
--   Bridge: card H0 comp equiv
-- statement:
--   The Bridge construction uses the card H0 comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/Transport.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/Transport.lean#L28-L39

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_Transport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]

theorem ReciprocityTheory.Neutral.Bridge.card_H0_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H0 (rho.comp (e : G →* G'))) = Nat.card (H0 rho) := by sorry
