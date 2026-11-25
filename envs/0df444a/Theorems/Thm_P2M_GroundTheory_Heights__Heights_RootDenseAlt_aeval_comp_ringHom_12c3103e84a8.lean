-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_comp_ringHom_12c3103e84a8
-- name    : P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_comp_ringHom_12c3103e84a8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:32.675651+00:00
-- url     : https://prove2.me/theorems/647d4c65-e8a3-5e3f-b88e-77f4a9bc3fd5
-- title:
--   P2 M Ground Theory Heights  Heights Root Dense Alt aeval comp ring Hom 12c3103e84a8: P2 M Ground Theory Heights  Heights Root Dense Alt aeval comp ring Hom 12c3103e84a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Dense Alt aeval comp ring Hom 12c3103e84a8 construction uses the P2 M Ground Theory Heights  Heights Root Dense Alt aeval comp ring Hom 12c3103e84a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDense.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDense.lean#L33-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDense
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootDenseAlt

theorem P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_comp_ringHom_12c3103e84a8 {σ τ Ω : Type*} [Field Ω] (φ : MvPolynomial σ ℚ →+* Ω)
    (P : τ → MvPolynomial σ ℚ) (g : MvPolynomial τ ℤ) :
    aeval (fun i => φ (P i)) g = φ (aeval P g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootDenseAlt».«aeval_comp_ringHom» := P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_comp_ringHom_12c3103e84a8
