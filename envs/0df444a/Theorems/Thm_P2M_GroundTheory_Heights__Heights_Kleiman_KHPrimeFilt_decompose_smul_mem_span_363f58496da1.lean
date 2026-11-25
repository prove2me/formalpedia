-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_decompose_smul_mem_span_363f58496da1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_decompose_smul_mem_span_363f58496da1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:44.382454+00:00
-- url     : https://prove2.me/theorems/ef2bc15a-f1ec-4dea-be7a-d02fa3be2e3c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt decompose smul mem span 363f58496da1: P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt decompose smul mem span 363f58496da1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt decompose smul mem span 363f58496da1 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt decompose smul mem span 363f58496da1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L81-L96

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_decompose_smul_mem_span_363f58496da1 (hgr : IsMGraded S ι 𝓜) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e)
    (r : MRingOver S ι) (c : K → ℤ) :
    (DirectSum.decompose 𝓜 (r • g) c : M) ∈ Submodule.span (MRingOver S ι) {g} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHPrimeFilt».«decompose_smul_mem_span» := P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_decompose_smul_mem_span_363f58496da1
