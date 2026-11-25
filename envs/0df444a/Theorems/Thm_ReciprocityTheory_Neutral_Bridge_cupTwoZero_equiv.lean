-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_cupTwoZero_equiv
-- name    : ReciprocityTheory.Neutral.Bridge.cupTwoZero_equiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:27.376657+00:00
-- url     : https://prove2.me/theorems/ce319f9a-87b1-44bf-9d39-5da92db2e6b6
-- title:
--   Bridge: cup Two Zero equiv
-- statement:
--   The Bridge construction uses the cup Two Zero equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean#L251-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean#L251-L261

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

theorem ReciprocityTheory.Neutral.Bridge.cupTwoZero_equiv (x : H2 (rho.comp (MonoidHom.id G')))
    (m : H0 ((twDual χ rho).comp (MonoidHom.id G'))) :
    cup20 (χ.comp (e : G →* G')) (rho.comp (e : G →* G')) (MonoidHom.id G)
        (equivH2OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
          (fun _ _ => rfl) x)
        (equivH0OfIso e _ _ (twDual_compat e χ rho) m) =
      equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl)
        (cup20 χ rho (MonoidHom.id G') x m) := by sorry
