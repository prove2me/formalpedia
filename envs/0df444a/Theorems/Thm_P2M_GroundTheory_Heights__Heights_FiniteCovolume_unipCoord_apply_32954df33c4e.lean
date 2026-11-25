-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipCoord_apply_32954df33c4e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipCoord_apply_32954df33c4e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:19.720566+00:00
-- url     : https://prove2.me/theorems/1f241658-dffc-5ffe-81a4-361421496d6b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume unip Coord apply 32954df33c4e: P2 M Ground Theory Heights  Heights Finite Covolume unip Coord apply 32954df33c4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume unip Coord apply 32954df33c4e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume unip Coord apply 32954df33c4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StUnipotentCoordProper.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StUnipotentCoordProper.lean#L22-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipCoord_apply_32954df33c4e (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (n : unipRadical h v x₀) (w : InfinitePlace E) :
    unipCoord h v x₀ w₀ n w =
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
        vecAt v w₀ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«unipCoord_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipCoord_apply_32954df33c4e
