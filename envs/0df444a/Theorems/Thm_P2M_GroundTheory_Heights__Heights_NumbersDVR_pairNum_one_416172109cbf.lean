-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_one_416172109cbf
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_one_416172109cbf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:43.467801+00:00
-- url     : https://prove2.me/theorems/7974ded6-d088-4d70-bb86-5d860a11ebc5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR pair Num one 416172109cbf: P2 M Ground Theory Heights  Heights Numbers DVR pair Num one 416172109cbf
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR pair Num one 416172109cbf construction uses the P2 M Ground Theory Heights  Heights Numbers DVR pair Num one 416172109cbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L532-L535
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L532-L535

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_one_416172109cbf (P : Ideal (MRing ι O)) (x : Fin N → K → ℤ)
    (Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ) (Q : List (K → ℤ)) :
    pairNum P x x (fun _ => 1) (fun _ => 1) Gs Q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pairNum_one» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_one_416172109cbf
