-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_posSemidef_of_intQuad_nonneg_ee0928ce48ea
-- name    : P2M_GroundTheory_Heights__Heights_Regular_posSemidef_of_intQuad_nonneg_ee0928ce48ea
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:27.041534+00:00
-- url     : https://prove2.me/theorems/8af566b0-39a8-405f-abc9-63a442591934
-- title:
--   P2 M Ground Theory Heights  Heights Regular pos Semidef of int Quad nonneg ee0928ce48ea: P2 M Ground Theory Heights  Heights Regular pos Semidef of int Quad nonneg ee0928ce48ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular pos Semidef of int Quad nonneg ee0928ce48ea construction uses the P2 M Ground Theory Heights  Heights Regular pos Semidef of int Quad nonneg ee0928ce48ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L146-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L146-L184

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_posSemidef_of_intQuad_nonneg_ee0928ce48ea {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (hB : Bᵀ = B)
    (h : ∀ v, 0 ≤ intQuad B v) : (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«posSemidef_of_intQuad_nonneg» := P2M_GroundTheory_Heights__Heights_Regular_posSemidef_of_intQuad_nonneg_ee0928ce48ea
