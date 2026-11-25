-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_finiteDimensional_weightedHomogeneousSubmodule_73afb5caf826
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_finiteDimensional_weightedHomogeneousSubmodule_73afb5caf826
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:58.727705+00:00
-- url     : https://prove2.me/theorems/59ba1d17-0c34-5b9f-a4ea-ff01061d72e4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR finite Dimensional weighted Homogeneous Submodule 73afb5caf826: P2 M Ground Theory Heights  Heights Numbers DVR finite Dimensional weighted Homogeneous
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR finite Dimensional weighted Homogeneous Submodule 73afb5caf826 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR finite Dimensional weighted Homogeneous Submodule 73afb5caf826 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGradedPieceQuot.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGradedPieceQuot.lean#L28-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
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
open MvPolynomial
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_finiteDimensional_weightedHomogeneousSubmodule_73afb5caf826 (F : Type u) [Field F] {K : Type}
    [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«finiteDimensional_weightedHomogeneousSubmodule» := P2M_GroundTheory_Heights__Heights_NumbersDVR_finiteDimensional_weightedHomogeneousSubmodule_73afb5caf826
