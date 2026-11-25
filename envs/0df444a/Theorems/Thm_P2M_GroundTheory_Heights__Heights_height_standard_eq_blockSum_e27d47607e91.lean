-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_standard_eq_blockSum_e27d47607e91
-- name    : P2M_GroundTheory_Heights__Heights_height_standard_eq_blockSum_e27d47607e91
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:49.151928+00:00
-- url     : https://prove2.me/theorems/ca449d16-f674-4a32-9c8b-aee14c847947
-- title:
--   P2 M Ground Theory Heights  Heights height standard eq block Sum e27d47607e91: P2 M Ground Theory Heights  Heights height standard eq block Sum e27d47607e91
-- statement:
--   The P2 M Ground Theory Heights  Heights height standard eq block Sum e27d47607e91 construction uses the P2 M Ground Theory Heights  Heights height standard eq block Sum e27d47607e91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L236-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L236-L247

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_height_standard_eq_blockSum_e27d47607e91 (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) :
    height (HermLine.standard n) x = ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
      ∑ k, blockSum (coordVec x) k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_standard_eq_blockSum» := P2M_GroundTheory_Heights__Heights_height_standard_eq_blockSum_e27d47607e91
