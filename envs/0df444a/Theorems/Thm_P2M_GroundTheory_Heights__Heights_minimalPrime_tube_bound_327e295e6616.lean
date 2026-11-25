-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_minimalPrime_tube_bound_327e295e6616
-- name    : P2M_GroundTheory_Heights__Heights_minimalPrime_tube_bound_327e295e6616
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:06.844808+00:00
-- url     : https://prove2.me/theorems/b74fff2d-e04d-455e-a9fc-062b92d7b2d1
-- title:
--   P2 M Ground Theory Heights  Heights minimal Prime tube bound 327e295e6616: P2 M Ground Theory Heights  Heights minimal Prime tube bound 327e295e6616
-- statement:
--   The P2 M Ground Theory Heights  Heights minimal Prime tube bound 327e295e6616 construction uses the P2 M Ground Theory Heights  Heights minimal Prime tube bound 327e295e6616 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetTubeVolume.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetTubeVolume.lean#L33-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetTubeVolume
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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_minimalPrime_tube_bound_327e295e6616 (h : PrimeTubeVolume.Statement) {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)}
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ)) (hK : IsCompact K)
    {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P ∈ I.minimalPrimes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (Metric.thickening r (zeroSet P ∩ K)) ≤
        ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«minimalPrime_tube_bound» := P2M_GroundTheory_Heights__Heights_minimalPrime_tube_bound_327e295e6616
