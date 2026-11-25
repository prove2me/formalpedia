-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_localLattice_swapAt_fbff93b7be3f
-- name    : P2M_GroundTheory_Heights__Heights_localLattice_swapAt_fbff93b7be3f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:02.049818+00:00
-- url     : https://prove2.me/theorems/14bfb4f8-3782-47d3-b53a-903245ef2f9f
-- title:
--   P2 M Ground Theory Heights  Heights local Lattice swap At fbff93b7be3f: P2 M Ground Theory Heights  Heights local Lattice swap At fbff93b7be3f
-- statement:
--   The P2 M Ground Theory Heights  Heights local Lattice swap At fbff93b7be3f construction uses the P2 M Ground Theory Heights  Heights local Lattice swap At fbff93b7be3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L223-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L223-L229

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

theorem P2M_GroundTheory_Heights__Heights_localLattice_swapAt_fbff93b7be3f (v₀ v : HeightOneSpectrum (𝓞 K)) :
    (localLattice v (FullLattice.standard K 2).carrier : Set _) =
      swapAt v₀ v '' localLattice v (FullLattice.standard K 2).carrier := by sorry

alias «GroundTheory».«Heights₂».«Heights».«localLattice_swapAt» := P2M_GroundTheory_Heights__Heights_localLattice_swapAt_fbff93b7be3f
