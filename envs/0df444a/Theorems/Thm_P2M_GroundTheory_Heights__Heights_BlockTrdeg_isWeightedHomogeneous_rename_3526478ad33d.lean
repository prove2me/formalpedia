-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_rename_3526478ad33d
-- name    : P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_rename_3526478ad33d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:56.176265+00:00
-- url     : https://prove2.me/theorems/a40e0ec7-4e7c-40bf-9431-892785941a76
-- title:
--   P2 M Ground Theory Heights  Heights Block Trdeg is Weighted Homogeneous rename 3526478ad33d: P2 M Ground Theory Heights  Heights Block Trdeg is Weighted Homogeneous rename 3526478ad33d
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Trdeg is Weighted Homogeneous rename 3526478ad33d construction uses the P2 M Ground Theory Heights  Heights Block Trdeg is Weighted Homogeneous rename 3526478ad33d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L94-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L94-L109

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
omit [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_rename_3526478ad33d (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : ∀ p, (v p).1 ∈ Set.range κ) (g : MvPolynomial (Σ k, ι k) ℤ) :
    IsWeightedHomogeneous (forgetWeight κ) (rename v g) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockTrdeg».«isWeightedHomogeneous_rename» := P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_rename_3526478ad33d
