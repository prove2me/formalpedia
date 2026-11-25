-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearIndependent_one_real_4f917615ceb5
-- name    : P2M_GroundTheory_Heights__Heights_linearIndependent_one_real_4f917615ceb5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:31.962238+00:00
-- url     : https://prove2.me/theorems/bd81bf13-f2b1-5908-885e-e913d21c99c4
-- title:
--   P2 M Ground Theory Heights  Heights linear Independent one real 4f917615ceb5: P2 M Ground Theory Heights  Heights linear Independent one real 4f917615ceb5
-- statement:
--   The P2 M Ground Theory Heights  Heights linear Independent one real 4f917615ceb5 construction uses the P2 M Ground Theory Heights  Heights linear Independent one real 4f917615ceb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L252-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L252-L256

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_linearIndependent_one_real_4f917615ceb5 : LinearIndependent ℝ ![(1 : ℝ)] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linearIndependent_one_real» := P2M_GroundTheory_Heights__Heights_linearIndependent_one_real_4f917615ceb5
