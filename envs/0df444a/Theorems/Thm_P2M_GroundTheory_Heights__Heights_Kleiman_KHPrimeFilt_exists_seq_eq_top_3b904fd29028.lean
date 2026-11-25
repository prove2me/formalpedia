-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_exists_seq_eq_top_3b904fd29028
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_exists_seq_eq_top_3b904fd29028
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:47.677794+00:00
-- url     : https://prove2.me/theorems/7be80d12-583c-57a6-a182-bd70f055015f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt exists seq eq top 3b904fd29028: P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt exists seq eq top 3b904fd29028
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt exists seq eq top 3b904fd29028 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt exists seq eq top 3b904fd29028 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L229-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L229-L241

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
variable (ι 𝓜)
variable {ι 𝓜}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_exists_seq_eq_top_3b904fd29028 [IsNoetherianRing S] [Module.Finite (MRingOver S ι) M]
    (hgr : IsMGraded S ι 𝓜) : ∃ n, seq ι 𝓜 n = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHPrimeFilt».«exists_seq_eq_top» := P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_exists_seq_eq_top_3b904fd29028
