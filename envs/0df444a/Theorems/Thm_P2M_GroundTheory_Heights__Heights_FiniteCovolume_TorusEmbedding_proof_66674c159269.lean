-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_proof_66674c159269
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_proof_66674c159269
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:01:35.148372+00:00
-- url     : https://prove2.me/theorems/7d7a02b0-27f9-4745-96dd-487f67d37a06
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding proof 66674c159269: P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding proof 66674c159269
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding proof 66674c159269 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding proof 66674c159269 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L186-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L186-L193

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramAtData_proof_6f69e474274d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_proof_66674c159269 (h : HermitianForm F E W) (v : Basis ι E W) (h1 : HermAtPlace.Statement h v)
    (h2 : GramAtData.Statement h v) : TorusEmbedding.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TorusEmbedding».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_proof_66674c159269
