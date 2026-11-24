-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPrime_of_divCycle_ne_zero_ba4bc8f68b63
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isPrime_of_divCycle_ne_zero_ba4bc8f68b63
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:25.732359+00:00
-- url     : https://prove2.me/theorems/cbe14cd5-b845-4abe-952e-63c61936e81d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Prime of div Cycle ne zero ba4bc8f68b63: P2 M Ground Theory Heights  Heights Numbers DVR is Prime of div Cycle ne zero ba4bc8f68b63
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Prime of div Cycle ne zero ba4bc8f68b63 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Prime of div Cycle ne zero ba4bc8f68b63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Statements.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Statements.lean#L51-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u v

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isPrime_of_divCycle_ne_zero_ba4bc8f68b63 {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    W.IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isPrime_of_divCycle_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isPrime_of_divCycle_ne_zero_ba4bc8f68b63
