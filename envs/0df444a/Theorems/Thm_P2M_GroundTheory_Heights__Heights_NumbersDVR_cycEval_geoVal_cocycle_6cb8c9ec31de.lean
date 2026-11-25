-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_geoVal_cocycle_6cb8c9ec31de
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_geoVal_cocycle_6cb8c9ec31de
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:11.027518+00:00
-- url     : https://prove2.me/theorems/c312610d-5fac-4fff-b1ba-8578be3fd489
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval geo Val cocycle 6cb8c9ec31de: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval geo Val cocycle 6cb8c9ec31de
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval geo Val cocycle 6cb8c9ec31de construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval geo Val cocycle 6cb8c9ec31de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L253-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L253-L281

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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_geoVal_cocycle_6cb8c9ec31de {A : Ideal (MRing ι R) → List (K → ℤ) → ℤ}
    {Z Z' : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (hZ' : (Function.support Z').Finite) (hp : ∀ W, PermInv (A W))
    (ha : ∀ W, Z W ≠ 0 → HeadAdd (A W)) (ha' : ∀ W, Z' W ≠ 0 → HeadAdd (A W)) (k : ℕ)
    (a b c : K → ℤ)
    (hC : ∀ l, cycEval (fun W => A W ((b - c) :: l)) Z = cycEval (fun W => A W ((a - b) :: l)) Z') :
    cycEval (fun W => geoVal (A W) k a c) (Z + Z') =
      cycEval (fun W => geoVal (A W) k a b) Z + cycEval (fun W => geoVal (A W) k b c) Z' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_geoVal_cocycle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_geoVal_cocycle_6cb8c9ec31de
