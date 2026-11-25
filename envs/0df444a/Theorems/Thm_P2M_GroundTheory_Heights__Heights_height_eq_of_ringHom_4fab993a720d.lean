-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_of_ringHom_4fab993a720d
-- name    : P2M_GroundTheory_Heights__Heights_height_eq_of_ringHom_4fab993a720d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:54.775373+00:00
-- url     : https://prove2.me/theorems/4be40baa-35a8-45a0-8259-bde3bf870a84
-- title:
--   P2 M Ground Theory Heights  Heights height eq of ring Hom 4fab993a720d: P2 M Ground Theory Heights  Heights height eq of ring Hom 4fab993a720d
-- statement:
--   The P2 M Ground Theory Heights  Heights height eq of ring Hom 4fab993a720d construction uses the P2 M Ground Theory Heights  Heights height eq of ring Hom 4fab993a720d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PPointHeightDegree.lean#L19-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PPointHeightDegree.lean#L19-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PPointHeightDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Module Matrix
open scoped ComplexOrder
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_height_eq_of_ringHom_4fab993a720d (A : HermLine n) {K' : Type*} [Field K'] [NumberField K']
    (τ : K' →+* AlgebraicClosure ℚ) (y : Cone n K') (hy : BlockNonzero y) :
    height A (fun k i ↦ τ (y k i)) = ((finrank ℚ K' : ℝ))⁻¹ *
      (∑ᶠ w : FinitePlace K', finiteTerm A w y +
        ∑ σ : K' →+* ℂ, Real.log (A.metric fun k i ↦ σ (y k i))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_eq_of_ringHom» := P2M_GroundTheory_Heights__Heights_height_eq_of_ringHom_4fab993a720d
