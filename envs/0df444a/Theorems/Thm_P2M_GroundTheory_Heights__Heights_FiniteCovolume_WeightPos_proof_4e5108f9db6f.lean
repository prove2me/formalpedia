-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightPos_proof_4e5108f9db6f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightPos_proof_4e5108f9db6f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:47:31.208428+00:00
-- url     : https://prove2.me/theorems/aeb544c4-b365-48c8-bc95-09b852afa459
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Weight Pos proof 4e5108f9db6f: P2 M Ground Theory Heights  Heights Finite Covolume Weight Pos proof 4e5108f9db6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Weight Pos proof 4e5108f9db6f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Weight Pos proof 4e5108f9db6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightPos.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightPos.lean#L14-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module Matrix
open scoped ComplexOrder
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightPos_proof_4e5108f9db6f (h : GroundTheory.Automorphic.HermitianForm F E W) (v : Basis ι E W)
    (h₁ : VecAtNeZero.Statement v) : WeightPos.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«WeightPos».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightPos_proof_4e5108f9db6f
