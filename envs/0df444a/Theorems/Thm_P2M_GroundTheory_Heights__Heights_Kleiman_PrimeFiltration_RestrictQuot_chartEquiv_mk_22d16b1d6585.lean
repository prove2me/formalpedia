-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_chartEquiv_mk_22d16b1d6585
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_chartEquiv_mk_22d16b1d6585
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:30.198976+00:00
-- url     : https://prove2.me/theorems/881ec467-7272-45e3-bde6-482bcf4a3b9e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot chart Equiv mk 22d16b1d6585: P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot chart Equiv mk 22d16b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot chart Equiv mk 22d16b1d6585 construction uses the P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot chart Equiv mk 22d16b1d6585 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrictQuotX.lean#L280-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrictQuotX.lean#L280-L284

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_chartEquiv_mk_22d16b1d6585 {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpy : primeOf (S := S) y = pp) (J : Chart y) (z : L.sub (liftChart hxy J)) :
    chartEquiv h hpy J (Submodule.Quotient.mk z) = chartMap h J z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«PrimeFiltration».«RestrictQuot».«chartEquiv_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_chartEquiv_mk_22d16b1d6585
