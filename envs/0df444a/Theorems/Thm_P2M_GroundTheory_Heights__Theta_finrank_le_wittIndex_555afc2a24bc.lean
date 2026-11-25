-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_finrank_le_wittIndex_555afc2a24bc
-- name    : P2M_GroundTheory_Heights__Theta_finrank_le_wittIndex_555afc2a24bc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:53:55.460986+00:00
-- url     : https://prove2.me/theorems/208993f2-66cb-44a7-bb76-bf82a87b07bf
-- title:
--   P2 M Ground Theory Heights  Theta finrank le witt Index 555afc2a24bc: P2 M Ground Theory Heights  Theta finrank le witt Index 555afc2a24bc
-- statement:
--   The P2 M Ground Theory Heights  Theta finrank le witt Index 555afc2a24bc construction uses the P2 M Ground Theory Heights  Theta finrank le witt Index 555afc2a24bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L136-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L136-L138

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

theorem P2M_GroundTheory_Heights__Theta_finrank_le_wittIndex_555afc2a24bc {W : Submodule E (ι → E)} (hW : IsTotallyIsotropic K H W) :
    finrank E W ≤ wittIndex K H := by sorry

alias «GroundTheory».«Heights₂».«Theta».«finrank_le_wittIndex» := P2M_GroundTheory_Heights__Theta_finrank_le_wittIndex_555afc2a24bc
