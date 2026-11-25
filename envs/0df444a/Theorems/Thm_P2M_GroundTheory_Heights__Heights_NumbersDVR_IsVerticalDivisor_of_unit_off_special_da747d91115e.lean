-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:49.242399+00:00
-- url     : https://prove2.me/theorems/bcd436d9-f98a-4f5a-b22d-71dbe1ff8759
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Is Vertical Divisor of unit off special da747d91115e: P2 M Ground Theory Heights  Heights Numbers DVR Is Vertical Divisor of unit off special da747d9111
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Is Vertical Divisor of unit off special da747d91115e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Is Vertical Divisor of unit off special da747d91115e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L117-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L117-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ}
    {f g : MRing ι O}
    (degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
      (fun k => (bf k : ℤ) - bg k) = b)
    (hf : f ∉ P) (hg : g ∉ P)
    (hunit : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
      (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    IsVerticalDivisor P ϖ b f g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IsVerticalDivisor».«of_unit_off_special» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e
