-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_isAlgebraic_of_mulVec_25b1546582a0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_isAlgebraic_of_mulVec_25b1546582a0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:28.89864+00:00
-- url     : https://prove2.me/theorems/f0b016d8-efa9-4c9f-b4f7-07c47dc1ac1f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg is Algebraic of mul Vec 25b1546582a0: P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg is Algebraic of mul Vec 25b1546582a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg is Algebraic of mul Vec 25b1546582a0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg is Algebraic of mul Vec 25b1546582a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeAlg.lean#L41-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeAlg.lean#L41-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
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
open GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_isAlgebraic_of_mulVec_25b1546582a0 {R L : Type*} [CommRing R] [IsDomain R] [CommRing L] [IsDomain L]
    [Algebra R L] {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n L) (w : n → L)
    (hG : ∀ i j, IsAlgebraic R (G i j)) (hGw : ∀ i, IsAlgebraic R ((G.mulVec w) i)) (hdet : G.det ≠ 0)
    (q : n) : IsAlgebraic R (w q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairConeAlg».«isAlgebraic_of_mulVec» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_isAlgebraic_of_mulVec_25b1546582a0
