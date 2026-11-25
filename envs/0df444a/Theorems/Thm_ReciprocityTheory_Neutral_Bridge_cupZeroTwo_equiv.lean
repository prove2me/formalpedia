-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_cupZeroTwo_equiv
-- name    : ReciprocityTheory.Neutral.Bridge.cupZeroTwo_equiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:05.620558+00:00
-- url     : https://prove2.me/theorems/35613950-5426-5b8e-90a7-234d871ddddd
-- title:
--   Bridge: cup Zero Two equiv
-- statement:
--   The Bridge construction uses the cup Zero Two equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean#L239-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean#L239-L249

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
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type}
  [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (e : G ≃ₜ* G') (χ : G' →* Rˣ) (rho : Representation R G' M)

theorem ReciprocityTheory.Neutral.Bridge.cupZeroTwo_equiv (m : H0 (rho.comp (MonoidHom.id G')))
    (y : H2 ((twDual χ rho).comp (MonoidHom.id G'))) :
    cupH0H2TwistedDual (χ.comp (e : G →* G')) (rho.comp (e : G →* G')) (MonoidHom.id G)
        (equivH0OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
          (fun _ _ => rfl) m)
        (equivH2OfIso e _ _ (twDual_compat e χ rho) y) =
      equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl)
        (cupH0H2TwistedDual χ rho (MonoidHom.id G') m y) := by sorry
