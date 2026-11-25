-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_equivH2OfIso_mk
-- name    : ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:14.490941+00:00
-- url     : https://prove2.me/theorems/91a76b51-2f75-4865-b97e-9d29c6493176
-- title:
--   Bridge: equiv H2 Of Iso mk
-- statement:
--   The Bridge construction uses the equiv H2 Of Iso mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean#L81-L83

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
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
variable {R : Type*} [CommRing R]
  {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (e : H ≃ₜ* G) (rho : Representation R G M) (rho' : Representation R H M)
  (hc : ∀ h m, rho (e h) m = rho' h m)

theorem ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk (f : Z2 rho) : equivH2OfIso e rho rho' hc (Submodule.Quotient.mk f) =
    Submodule.Quotient.mk (compatiblePairCocycles2 rho rho' (e : H →* G) (continuous_coe_iso e) LinearMap.id
      continuous_id hc f) := by sorry
