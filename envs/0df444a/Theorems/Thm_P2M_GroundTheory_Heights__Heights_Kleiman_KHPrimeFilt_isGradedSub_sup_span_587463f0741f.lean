-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isGradedSub_sup_span_587463f0741f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isGradedSub_sup_span_587463f0741f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:36:07.926995+00:00
-- url     : https://prove2.me/theorems/fb7fb9d9-4a96-5cd7-97da-155f773543c8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt is Graded Sub sup span 587463f0741f: P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt is Graded Sub sup span 587463f0741f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt is Graded Sub sup span 587463f0741f construction uses the P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt is Graded Sub sup span 587463f0741f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L103-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} [DirectSum.Decomposition 𝓜]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isGradedSub_sup_span_587463f0741f (hgr : IsMGraded S ι 𝓜) {A : Submodule (MRingOver S ι) M}
    (hA : IsGradedSub 𝓜 A) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e) :
    IsGradedSub 𝓜 (A ⊔ Submodule.span (MRingOver S ι) {g}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHPrimeFilt».«isGradedSub_sup_span» := P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isGradedSub_sup_span_587463f0741f
