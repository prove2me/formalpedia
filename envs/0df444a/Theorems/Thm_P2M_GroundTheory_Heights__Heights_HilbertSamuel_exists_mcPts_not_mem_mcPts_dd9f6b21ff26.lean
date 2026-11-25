-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_mcPts_not_mem_mcPts_dd9f6b21ff26
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_mcPts_not_mem_mcPts_dd9f6b21ff26
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:37.824801+00:00
-- url     : https://prove2.me/theorems/026e53d1-1ccf-4d21-bfbd-620eb1a97da7
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel exists mc Pts not mem mc Pts dd9f6b21ff26: P2 M Ground Theory Heights  Heights Hilbert Samuel exists mc Pts not mem mc Pts dd9f6b21ff26
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel exists mc Pts not mem mc Pts dd9f6b21ff26 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel exists mc Pts not mem mc Pts dd9f6b21ff26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GenericComplexPoint.lean#L34-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GenericComplexPoint.lean#L34-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_mcPts_not_mem_mcPts_dd9f6b21ff26 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (hJ : ¬ J ≤ P) :
    ∃ z, z ∈ mcPts P ∧ z ∉ mcPts J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«exists_mcPts_not_mem_mcPts» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_mcPts_not_mem_mcPts_dd9f6b21ff26
