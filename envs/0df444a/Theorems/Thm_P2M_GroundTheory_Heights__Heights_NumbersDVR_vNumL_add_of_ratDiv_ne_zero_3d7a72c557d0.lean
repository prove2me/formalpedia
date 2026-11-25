-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_of_ratDiv_ne_zero_3d7a72c557d0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_of_ratDiv_ne_zero_3d7a72c557d0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:33.945333+00:00
-- url     : https://prove2.me/theorems/dbe0e33f-26f3-54cc-9a7f-4a5097d75231
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR v Num L add of rat Div ne zero 3d7a72c557d0: P2 M Ground Theory Heights  Heights Numbers DVR v Num L add of rat Div ne zero 3d7a72c557d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR v Num L add of rat Div ne zero 3d7a72c557d0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR v Num L add of rat Div ne zero 3d7a72c557d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L269-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L269-L313

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_of_ratDiv_ne_zero_3d7a72c557d0 {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} {e : ℕ} (hP : IsModelOver P (e + 1))
    {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g) {W : Ideal (MRing ι O)}
    (hW : ratDiv P f g W ≠ 0) (a₁ a₂ : K → ℤ) (l : List (K → ℤ)) (hl : e ≤ l.length) :
    vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«vNumL_add_of_ratDiv_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_of_ratDiv_ne_zero_3d7a72c557d0
