-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_cycEval_family_d251d12bebba
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_cycEval_family_d251d12bebba
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:10:07.060386+00:00
-- url     : https://prove2.me/theorems/a2ea5369-3cf4-42f5-914c-48c5404ef986
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting cyc Eval family d251d12bebba: P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting cyc Eval family d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting cyc Eval family d251d12bebba construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting cyc Eval family d251d12bebba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L81-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L81-L103

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_cycEval_family_d251d12bebba (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) {ϖ : O}
    (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {n : ℕ} (hP : IsModelOver P (n + 1)) {b : K → ℤ}
    {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g)
    (Iκ : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection Iκ) (M : Fin (n + 1) → K → ℤ) :
    cycEval (fun W => Iκ (specialIdeal W) (n + 1) M) (ratDiv P f g) =
      cycEval (fun W => vNum W M) (ratDiv P f g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«VerticalDivisorsCommuting».«cycEval_family» := P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_cycEval_family_d251d12bebba
