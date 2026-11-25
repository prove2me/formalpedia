-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_maximalSpectrum_ord_eq_sum_665bea89a1e0
-- name    : P2M_GroundTheory_Heights__Heights_finsum_maximalSpectrum_ord_eq_sum_665bea89a1e0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:25.722139+00:00
-- url     : https://prove2.me/theorems/4f87a414-3928-41b6-a568-830703c0ef12
-- title:
--   P2 M Ground Theory Heights  Heights finsum maximal Spectrum ord eq sum 665bea89a1e0: P2 M Ground Theory Heights  Heights finsum maximal Spectrum ord eq sum 665bea89a1e0
-- statement:
--   The P2 M Ground Theory Heights  Heights finsum maximal Spectrum ord eq sum 665bea89a1e0 construction uses the P2 M Ground Theory Heights  Heights finsum maximal Spectrum ord eq sum 665bea89a1e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLength.lean#L11-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLength.lean#L11-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_finsum_maximalSpectrum_ord_eq_sum_665bea89a1e0 {O B ι : Type*} [CommRing O] [CommRing B] [Algebra O B] (θ : B)
    (S : Finset ι) (c : ι → Ideal B) (hc : Set.BijOn c ↑S {P | P.IsMaximal ∧ θ ∈ P}) (m : ι → ℕ∞)
    (hm : ∀ i ∈ S, ∀ _ : (c i).IsPrime,
      Ring.ord (Localization.AtPrime (c i)) (algebraMap B _ θ) * Module.length O (B ⧸ c i) = m i) :
    ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal) =
      ∑ i ∈ S, m i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finsum_maximalSpectrum_ord_eq_sum» := P2M_GroundTheory_Heights__Heights_finsum_maximalSpectrum_ord_eq_sum_665bea89a1e0
