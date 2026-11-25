-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_DiagonalChange_proof_8ff81c4b2bba
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_DiagonalChange_proof_8ff81c4b2bba
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:10.163785+00:00
-- url     : https://prove2.me/theorems/5d156df6-1a3b-50df-9e0a-4ad59121cb61
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Diagonal Change proof 8ff81c4b2bba: P2 M Ground Theory Heights  Heights Lattice Lemmas Diagonal Change proof 8ff81c4b2bba
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Diagonal Change proof 8ff81c4b2bba construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Diagonal Change proof 8ff81c4b2bba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PDiagonalChange.lean#L100-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PDiagonalChange.lean#L100-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_DiagonalChange_proof_8ff81c4b2bba : DiagonalChange.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«DiagonalChange».«proof» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_DiagonalChange_proof_8ff81c4b2bba
