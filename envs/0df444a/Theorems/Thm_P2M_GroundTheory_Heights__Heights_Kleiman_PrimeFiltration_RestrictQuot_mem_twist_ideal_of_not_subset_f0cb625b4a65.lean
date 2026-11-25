-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_mem_twist_ideal_of_not_subset_f0cb625b4a65
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_mem_twist_ideal_of_not_subset_f0cb625b4a65
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:09.860956+00:00
-- url     : https://prove2.me/theorems/8b1d1823-5a89-59ce-acea-dc6360f9f7a7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot mem twist ideal of not subset f0cb625b4a65: P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot mem tw
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot mem twist ideal of not subset f0cb625b4a65 construction uses the P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot mem twist ideal of not subset f0cb625b4a65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrictQuotX.lean#L216-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrictQuotX.lean#L216-L228

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_mem_twist_ideal_of_not_subset_f0cb625b4a65 {pp : Ideal (Poly S N)} (hpp : primeOf (S := S) y ≤ pp)
    (F : SubSystem S x Ω) (I : Chart x) (hI : ¬ I.1 ⊆ support y) {z : Ω} (hz : z ∈ F.sub I) :
    z ∈ (F.twist (idealSys x pp)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«PrimeFiltration».«RestrictQuot».«mem_twist_ideal_of_not_subset» := P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_mem_twist_ideal_of_not_subset_f0cb625b4a65
