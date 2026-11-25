-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_quotH_equiv_a468c3a14426
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_quotH_equiv_a468c3a14426
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:09.717645+00:00
-- url     : https://prove2.me/theorems/5cab33e2-45c4-4854-966f-0904229b2b53
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot quot H equiv a468c3a14426: P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot quot H equiv a468c3a144
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot quot H equiv a468c3a14426 construction uses the P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot quot H equiv a468c3a14426 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrictQuotX.lean#L286-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrictQuotX.lean#L286-L301

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrictQuotX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_quotH_equiv_a468c3a14426 {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpy : primeOf (S := S) y = pp) (i : ℕ) :
    Nonempty (SubSystem.quotH L.toSubSystem (L.toSubSystem.twist (idealSys x pp)) i ≃ₗ[S]
      L'.toSubSystem.H i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«PrimeFiltration».«RestrictQuot».«quotH_equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_quotH_equiv_a468c3a14426
