-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_isProjVarF_specialIdeal_030bb55b1723
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_isProjVarF_specialIdeal_030bb55b1723
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:10:27.089076+00:00
-- url     : https://prove2.me/theorems/37672bfd-ab18-4fcb-a2d9-ea59d6289e07
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting is Proj Var F special Ideal 030bb55b1723: P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting is Pro
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting is Proj Var F special Ideal 030bb55b1723 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting is Proj Var F special Ideal 030bb55b1723 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L61-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L61-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByFormField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivCycleSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WeilNumbersImpVerticalDivisorsCommute
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
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorsCommuting
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_isProjVarF_specialIdeal_030bb55b1723 (hDim : ComponentDim.Statement.{u}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {a : K → ℕ} {f : MRing ι O}
    (hf : IsMultiHomog f a) (hfP : f ∉ P) {W : Ideal (MRing ι O)} (hW : divCycle P f W ≠ 0)
    (hϖW : (C ϖ : MRing ι O) ∈ W) : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«VerticalDivisorsCommuting».«isProjVarF_specialIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_isProjVarF_specialIdeal_030bb55b1723
