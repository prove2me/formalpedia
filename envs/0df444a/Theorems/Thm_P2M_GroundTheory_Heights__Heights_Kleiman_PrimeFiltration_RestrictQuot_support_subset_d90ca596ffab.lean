-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_support_subset_d90ca596ffab
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_support_subset_d90ca596ffab
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:02.270191+00:00
-- url     : https://prove2.me/theorems/1e906d54-fe4c-49e4-8025-0b5d647c8c3a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot support subset d90ca596ffab: P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot support subset d90ca5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot support subset d90ca596ffab construction uses the P2 M Ground Theory Heights  Heights Kleiman Prime Filtration Restrict Quot support subset d90ca596ffab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrictQuotX.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrictQuotX.lean#L135-L136

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_support_subset_d90ca596ffab (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) : support y ⊆ support x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«PrimeFiltration».«RestrictQuot».«support_subset» := P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_support_subset_d90ca596ffab
