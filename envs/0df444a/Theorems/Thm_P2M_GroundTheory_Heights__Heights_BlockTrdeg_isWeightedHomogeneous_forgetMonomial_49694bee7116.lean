-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_forgetMonomial_49694bee7116
-- name    : P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_forgetMonomial_49694bee7116
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:42.485079+00:00
-- url     : https://prove2.me/theorems/7a201d36-3b5a-466f-879d-9b79d6a70d8a
-- title:
--   P2 M Ground Theory Heights  Heights Block Trdeg is Weighted Homogeneous forget Monomial 49694bee7116: P2 M Ground Theory Heights  Heights Block Trdeg is Weighted Homogeneous forget Monomial 49694bee71
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Trdeg is Weighted Homogeneous forget Monomial 49694bee7116 construction uses the P2 M Ground Theory Heights  Heights Block Trdeg is Weighted Homogeneous forget Monomial 49694bee7116 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L116-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L116-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
variable {K : Type} {K' : Type} [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_forgetMonomial_49694bee7116 (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1)
    (a : Forgotten κ →₀ ℕ) :
    IsWeightedHomogeneous (forgetWeight κ) (forgetMonomial κ i a) ⇑a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockTrdeg».«isWeightedHomogeneous_forgetMonomial» := P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_forgetMonomial_49694bee7116
