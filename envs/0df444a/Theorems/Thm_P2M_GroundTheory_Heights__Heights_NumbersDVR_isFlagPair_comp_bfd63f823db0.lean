-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_comp_bfd63f823db0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_comp_bfd63f823db0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:10:54.068462+00:00
-- url     : https://prove2.me/theorems/2f8dce5a-fdc4-4484-98d0-b49628c6d243
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair comp bfd63f823db0: P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair comp bfd63f823db0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair comp bfd63f823db0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair comp bfd63f823db0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L488-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L488-L513

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_comp_bfd63f823db0 {ϖ : O} {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime]
    {B B' B'' : ChartBundle O (segreVec y) N E} {w w' w'' : Module.Basis (Fin N) Ω E}
    {x x' x'' : Fin N → K → ℤ} {f g f' g' : Fin N → MRing ι O}
    (hp₁ : IsFlagPair ϖ y B B' w w' x x' f g) (hp₂ : IsFlagPair ϖ y B' B'' w' w'' x' x'' f' g') :
    IsFlagPair ϖ y B B'' w w'' x x'' (fun i => f i * f' i) (fun i => g i * g' i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isFlagPair_comp» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_comp_bfd63f823db0
