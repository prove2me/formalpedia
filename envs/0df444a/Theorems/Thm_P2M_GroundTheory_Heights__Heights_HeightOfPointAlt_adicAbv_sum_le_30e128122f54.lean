-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_sum_le_30e128122f54
-- name    : P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_sum_le_30e128122f54
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:10.89885+00:00
-- url     : https://prove2.me/theorems/238b4311-36b8-56c2-b140-0683a08070ae
-- title:
--   P2 M Ground Theory Heights  Heights Height Of Point Alt adic Abv sum le 30e128122f54: P2 M Ground Theory Heights  Heights Height Of Point Alt adic Abv sum le 30e128122f54
-- statement:
--   The P2 M Ground Theory Heights  Heights Height Of Point Alt adic Abv sum le 30e128122f54 construction uses the P2 M Ground Theory Heights  Heights Height Of Point Alt adic Abv sum le 30e128122f54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean#L16-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint
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
open MvPolynomial NumberField ComplexAt TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfPointAlt
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_sum_le_30e128122f54 (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (s : Finset ι)
    (f : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ i ∈ s, NumberField.HeightOneSpectrum.adicAbv K v (f i) ≤ r) :
    NumberField.HeightOneSpectrum.adicAbv K v (∑ i ∈ s, f i) ≤ r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightOfPointAlt».«adicAbv_sum_le» := P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_sum_le_30e128122f54
