-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isMultiHomogIdeal_of_isHomogeneous_45acc6349d53
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isMultiHomogIdeal_of_isHomogeneous_45acc6349d53
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:13.234601+00:00
-- url     : https://prove2.me/theorems/9fc6c817-97fa-4d1a-b0e6-36452320315b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt is Multi Homog Ideal of is Homogeneous 45acc6349d53: P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt is Multi Homog Ideal of is Homoge
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt is Multi Homog Ideal of is Homogeneous 45acc6349d53 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt is Multi Homog Ideal of is Homogeneous 45acc6349d53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L129-L135

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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 2000] lexDecEq

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isMultiHomogIdeal_of_isHomogeneous_45acc6349d53 {I : Ideal (MRingOver S ι)}
    (h : I.IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι))) : IsMultiHomogIdeal I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHPrimeFilt».«isMultiHomogIdeal_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isMultiHomogIdeal_of_isHomogeneous_45acc6349d53
