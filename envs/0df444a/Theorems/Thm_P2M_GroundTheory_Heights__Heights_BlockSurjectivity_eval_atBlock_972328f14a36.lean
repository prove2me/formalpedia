-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_972328f14a36
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_972328f14a36
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:52.334876+00:00
-- url     : https://prove2.me/theorems/eb550ae8-5c51-405e-a814-b40b26e6f2e4
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity eval at Block 972328f14a36: P2 M Ground Theory Heights  Heights Block Surjectivity eval at Block 972328f14a36
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity eval at Block 972328f14a36 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity eval at Block 972328f14a36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L76-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_972328f14a36 (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (x : Coord n → ℂ)
    (q : MvPolynomial (Coord n) ℤ) :
    eval x (atBlock k₀ w q) = evalCone (withBlock k₀ (w ()) x) q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«eval_atBlock» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_972328f14a36
