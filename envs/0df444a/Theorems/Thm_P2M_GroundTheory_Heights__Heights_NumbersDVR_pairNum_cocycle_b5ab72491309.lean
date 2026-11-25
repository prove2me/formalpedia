-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_cocycle_b5ab72491309
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_cocycle_b5ab72491309
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:00.568545+00:00
-- url     : https://prove2.me/theorems/6a830b1b-26dc-42df-a964-3e029d4e7cb2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR pair Num cocycle b5ab72491309: P2 M Ground Theory Heights  Heights Numbers DVR pair Num cocycle b5ab72491309
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR pair Num cocycle b5ab72491309 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR pair Num cocycle b5ab72491309 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L570-L612
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L570-L612

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_cocycle_b5ab72491309 (hFI : FlagIndependence.Statement)
    (hC2 : VerticalDivisorsCommute.Statement.{0}) (h3 : IntNumAddFirst.Statement.{0})
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {d : ℕ} (hP : IsModelOver (pointIdeal O y) d)
    {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {B B' B'' : ChartBundle O (segreVec y) N E}
    (hS : SameGenericFibre ϖ B B') (hS' : SameGenericFibre ϖ B' B'')
    {w w' w'' : Module.Basis (Fin N) Ω E} {x x' x'' : Fin N → K → ℤ}
    {f g f' g' f'' g'' : Fin N → MRing ι O}
    (hp₁ : IsFlagPair ϖ y B B' w w' x x' f g) (hp₂ : IsFlagPair ϖ y B' B'' w' w'' x' x'' f' g')
    (hp₃ : IsFlagPair ϖ y B B'' w w'' x x'' f'' g'')
    {k : ℕ} {Gs Gs' Gs'' : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ}
    (hG : IsPairExpansion k (psum (Fin N) ℤ k) Gs) (hG' : IsPairExpansion k (psum (Fin N) ℤ k) Gs')
    (hG'' : IsPairExpansion k (psum (Fin N) ℤ k) Gs'')
    {Q : List (K → ℤ)} (hQ : Q.length + k = d + 1) :
    pairNum (pointIdeal O y) x x'' f'' g'' Gs'' Q =
      pairNum (pointIdeal O y) x x' f g Gs Q + pairNum (pointIdeal O y) x' x'' f' g' Gs' Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pairNum_cocycle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_cocycle_b5ab72491309
