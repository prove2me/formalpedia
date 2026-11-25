-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_localLattice_span_d9c3f7370b5e
-- name    : P2M_GroundTheory_Heights__Heights_localLattice_span_d9c3f7370b5e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:44.253099+00:00
-- url     : https://prove2.me/theorems/4c9c44f1-08de-4729-a2fe-384bde7a565f
-- title:
--   P2 M Ground Theory Heights  Heights local Lattice span d9c3f7370b5e: P2 M Ground Theory Heights  Heights local Lattice span d9c3f7370b5e
-- statement:
--   The P2 M Ground Theory Heights  Heights local Lattice span d9c3f7370b5e construction uses the P2 M Ground Theory Heights  Heights local Lattice span d9c3f7370b5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L125-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L125-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (v : HeightOneSpectrum (𝓞 K))

theorem P2M_GroundTheory_Heights__Heights_localLattice_span_d9c3f7370b5e (S : Set V) :
    localLattice v (Submodule.span (𝓞 K) S) = Submodule.span _ (toLocal v '' S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«localLattice_span» := P2M_GroundTheory_Heights__Heights_localLattice_span_d9c3f7370b5e
