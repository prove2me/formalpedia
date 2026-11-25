-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_commute_6f4d606e4172
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_commute_6f4d606e4172
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:06.456926+00:00
-- url     : https://prove2.me/theorems/2f1af27d-af4a-4a04-95e1-8dc3f8af0f92
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR list Num commute 6f4d606e4172: P2 M Ground Theory Heights  Heights Numbers DVR list Num commute 6f4d606e4172
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR list Num commute 6f4d606e4172 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR list Num commute 6f4d606e4172 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L393-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L393-L406

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
universe u
variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_commute_6f4d606e4172 (hC2 : VerticalDivisorsCommute.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b b' : K → ℤ} {f g f' g' : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hD' : IsVerticalDivisor P ϖ b' f' g')
    (Q l : List (K → ℤ)) :
    cycEval (fun W => listNum W Q d (b' :: l)) (ratDiv P f g) =
      cycEval (fun W => listNum W Q d (b :: l)) (ratDiv P f' g') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«listNum_commute» := P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_commute_6f4d606e4172
