-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DualityFor_of_comp
-- name    : ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:45.635516+00:00
-- url     : https://prove2.me/theorems/51f8c268-ebe3-4d3e-b4be-6abcbd7eaa98
-- title:
--   Duality For: of comp
-- statement:
--   The Duality For construction uses the of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/Transport.lean#L248-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/Transport.lean#L248-L281

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

theorem ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp (e : G ≃ₜ* G') (χ : G' →* Rˣ) {rho : Representation R G' M} (hrho : ContAction rho)
    (h : DualityFor (χ.comp (e : G →* G')) (rho.comp (e : G →* G')) (contAction_comp e hrho)) :
    DualityFor χ rho hrho := by sorry
