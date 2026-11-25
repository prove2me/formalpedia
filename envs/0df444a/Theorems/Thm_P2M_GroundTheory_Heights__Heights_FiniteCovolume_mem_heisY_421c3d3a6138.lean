-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_heisY_421c3d3a6138
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_heisY_421c3d3a6138
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:08:43.235654+00:00
-- url     : https://prove2.me/theorems/9c2d62f8-817d-4cc8-9080-f55242719cfe
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume mem heis Y 421c3d3a6138: P2 M Ground Theory Heights  Heights Finite Covolume mem heis Y 421c3d3a6138
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume mem heis Y 421c3d3a6138 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume mem heis Y 421c3d3a6138 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusCoords.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusCoords.lean#L59-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_heisY_421c3d3a6138 {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
    {y : InfinitePlace E → ι → ℂ} : y ∈ heisY h v x₀ w₀ ↔
      ∀ w, hForm (gramAt h v w) (vecAt v x₀ w) (y w) = 0 ∧
        hForm (gramAt h v w) (vecAt v w₀ w) (y w) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«mem_heisY» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_heisY_421c3d3a6138
