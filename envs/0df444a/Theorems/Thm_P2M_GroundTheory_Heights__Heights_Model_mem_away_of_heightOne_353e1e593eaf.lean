-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_away_of_heightOne_353e1e593eaf
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_away_of_heightOne_353e1e593eaf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:30.596278+00:00
-- url     : https://prove2.me/theorems/696244fe-2225-4cf7-bb6e-3e9e62dd81cf
-- title:
--   P2 M Ground Theory Heights  Heights Model mem away of height One 353e1e593eaf: P2 M Ground Theory Heights  Heights Model mem away of height One 353e1e593eaf
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem away of height One 353e1e593eaf construction uses the P2 M Ground Theory Heights  Heights Model mem away of height One 353e1e593eaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PAwayHeightOne.lean#L9-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PAwayHeightOne.lean#L9-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PAwayHeightOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_mem_away_of_heightOne_353e1e593eaf (hHOI : HeightOneIntersection.Statement)
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (Ω : Type) [Field Ω] [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω))
    (h : A) (hh : h ≠ 0) (a : Ω)
    (hs : ∃ s : A, s ≠ 0 ∧ ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n * s) * a = algebraMap A Ω g)
    (hP : ∀ P : Ideal A, P.IsPrime → P.height = 1 → h ∉ P →
      ∃ t : A, t ∉ P ∧ ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n * t) * a = algebraMap A Ω g) :
    ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n) * a = algebraMap A Ω g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_away_of_heightOne» := P2M_GroundTheory_Heights__Heights_Model_mem_away_of_heightOne_353e1e593eaf
