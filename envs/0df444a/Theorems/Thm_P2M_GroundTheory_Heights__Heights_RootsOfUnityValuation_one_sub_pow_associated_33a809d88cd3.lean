-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_one_sub_pow_associated_33a809d88cd3
-- name    : P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_one_sub_pow_associated_33a809d88cd3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:01.225158+00:00
-- url     : https://prove2.me/theorems/d180fb6f-8c38-406e-a02b-207a48169916
-- title:
--   P2 M Ground Theory Heights  Heights Roots Of Unity Valuation one sub pow associated 33a809d88cd3: P2 M Ground Theory Heights  Heights Roots Of Unity Valuation one sub pow associated 33a809d88cd3
-- statement:
--   The P2 M Ground Theory Heights  Heights Roots Of Unity Valuation one sub pow associated 33a809d88cd3 construction uses the P2 M Ground Theory Heights  Heights Roots Of Unity Valuation one sub pow associated 33a809d88cd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PRootsOfUnityValuation.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PRootsOfUnityValuation.lean#L20-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PRootsOfUnityValuation
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
open NumberField Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RootsOfUnityValuation
variable {A : Type*} [CommRing A] [IsDomain A]

theorem P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_one_sub_pow_associated_33a809d88cd3 {l : ℕ} (hl : l.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ l) :
    Associated ((1 - ζ) ^ (l - 1)) (l : A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootsOfUnityValuation».«one_sub_pow_associated» := P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_one_sub_pow_associated_33a809d88cd3
