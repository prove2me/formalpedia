-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_headAdd_f9a6774e0aa2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_headAdd_f9a6774e0aa2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:07.210388+00:00
-- url     : https://prove2.me/theorems/db947488-c3ea-42f2-98bd-8aa8f4d2294d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR list Num head Add f9a6774e0aa2: P2 M Ground Theory Heights  Heights Numbers DVR list Num head Add f9a6774e0aa2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR list Num head Add f9a6774e0aa2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR list Num head Add f9a6774e0aa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L382-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L382-L391

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_headAdd_f9a6774e0aa2 (h3 : IntNumAddFirst.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) {W : Ideal (MRing ι O)} (hW : ratDiv P f g W ≠ 0)
    (Q : List (K → ℤ)) : HeadAdd (listNum W Q d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«listNum_headAdd» := P2M_GroundTheory_Heights__Heights_NumbersDVR_listNum_headAdd_f9a6774e0aa2
