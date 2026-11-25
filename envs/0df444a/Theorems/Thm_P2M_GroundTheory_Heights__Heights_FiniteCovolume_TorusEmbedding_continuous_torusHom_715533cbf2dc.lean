-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_continuous_torusHom_715533cbf2dc
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_continuous_torusHom_715533cbf2dc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:16.59244+00:00
-- url     : https://prove2.me/theorems/71e9f6ec-07c1-5224-978e-3535ddf4c40b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding continuous torus Hom 715533cbf2dc: P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding continuous torus Hom 715533cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding continuous torus Hom 715533cbf2dc construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding continuous torus Hom 715533cbf2dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L167-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L167-L176

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
variable {h : HermitianForm F E W} {v : Basis ι E W}
variable (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
  (hp : IsHyperbolicPair h x₀ w₀)

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_continuous_torusHom_715533cbf2dc : Continuous (torusHom h1 h2 hp) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TorusEmbedding».«continuous_torusHom» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_continuous_torusHom_715533cbf2dc
