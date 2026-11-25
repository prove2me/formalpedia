-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_head_1a96cf9f98d0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_head_1a96cf9f98d0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:19:21.744166+00:00
-- url     : https://prove2.me/theorems/5784d05b-58b9-548c-8b0e-5b53608e8dc6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR v Num L add head 1a96cf9f98d0: P2 M Ground Theory Heights  Heights Numbers DVR v Num L add head 1a96cf9f98d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR v Num L add head 1a96cf9f98d0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR v Num L add head 1a96cf9f98d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L335-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L335-L380

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_head_1a96cf9f98d0 (h3 : IntNumAddFirst.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) {W : Ideal (MRing ι O)} (hW : ratDiv P f g W ≠ 0)
    (u v : K → ℤ) (l : List (K → ℤ)) (hl : l.length + 1 = d) :
    vNumL W ((u + v) :: l) = vNumL W (u :: l) + vNumL W (v :: l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«vNumL_add_head» := P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_head_1a96cf9f98d0
