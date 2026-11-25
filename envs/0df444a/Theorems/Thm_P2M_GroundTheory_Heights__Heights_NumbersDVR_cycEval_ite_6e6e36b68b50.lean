-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_ite_6e6e36b68b50
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_ite_6e6e36b68b50
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:57.92471+00:00
-- url     : https://prove2.me/theorems/bcd4d46c-3175-4d46-80c8-1936557a55cb
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval ite 6e6e36b68b50: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval ite 6e6e36b68b50
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval ite 6e6e36b68b50 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval ite 6e6e36b68b50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L43-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
omit [Fintype K] [DecidableEq K]
open Classical

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_ite_6e6e36b68b50 (p : Ideal (MRing ι R) → Prop) (A B : Ideal (MRing ι R) → ℤ)
    (Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => if p W then A W else B W) Z =
      cycEval (fun W => if p W then A W else 0) Z + cycEval (fun W => if p W then 0 else B W) Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_ite» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_ite_6e6e36b68b50
