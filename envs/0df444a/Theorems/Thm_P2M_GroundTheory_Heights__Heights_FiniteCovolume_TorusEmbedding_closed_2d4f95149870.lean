-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_closed_2d4f95149870
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_closed_2d4f95149870
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:13:38.190153+00:00
-- url     : https://prove2.me/theorems/8da46c90-82a7-5799-9b67-a29b9e40ff7e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding closed 2d4f95149870: P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding closed 2d4f95149870
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding closed 2d4f95149870 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding closed 2d4f95149870 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L195-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L195-L196

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.TorusEmbedding
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_closed_2d4f95149870 (h : HermitianForm F E W) (v : Basis ι E W) : TorusEmbedding.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TorusEmbedding».«closed» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_closed_2d4f95149870
