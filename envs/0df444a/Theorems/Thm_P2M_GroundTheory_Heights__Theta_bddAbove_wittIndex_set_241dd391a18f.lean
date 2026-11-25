-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_bddAbove_wittIndex_set_241dd391a18f
-- name    : P2M_GroundTheory_Heights__Theta_bddAbove_wittIndex_set_241dd391a18f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:36.673284+00:00
-- url     : https://prove2.me/theorems/7f512263-7ce6-45af-b76d-10f357c30c06
-- title:
--   P2 M Ground Theory Heights  Theta bdd Above witt Index set 241dd391a18f: P2 M Ground Theory Heights  Theta bdd Above witt Index set 241dd391a18f
-- statement:
--   The P2 M Ground Theory Heights  Theta bdd Above witt Index set 241dd391a18f construction uses the P2 M Ground Theory Heights  Theta bdd Above witt Index set 241dd391a18f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L129-L134

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E)
variable {K H}
variable (K H)
variable {K H}
variable (K H)
variable {K H}

theorem P2M_GroundTheory_Heights__Theta_bddAbove_wittIndex_set_241dd391a18f :
    BddAbove {d | ∃ W : Submodule E (ι → E), IsTotallyIsotropic K H W ∧ finrank E W = d} := by sorry

alias «GroundTheory».«Heights₂».«Theta».«bddAbove_wittIndex_set» := P2M_GroundTheory_Heights__Theta_bddAbove_wittIndex_set_241dd391a18f
