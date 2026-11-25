-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_le_of_posSemidef_smul_sub_78b4f18cf645
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_le_of_posSemidef_smul_sub_78b4f18cf645
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:24.687463+00:00
-- url     : https://prove2.me/theorems/a59d0b73-d83f-4188-b4dc-55792fd652e0
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas re det le of pos Semidef smul sub 78b4f18cf645: P2 M Ground Theory Heights  Heights Lattice Lemmas re det le of pos Semidef smul sub 78b4f18cf645
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas re det le of pos Semidef smul sub 78b4f18cf645 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas re det le of pos Semidef smul sub 78b4f18cf645 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PNormComparison.lean#L13-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PNormComparison.lean#L13-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PNormComparison
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
open scoped ComplexOrder MatrixOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_le_of_posSemidef_smul_sub_78b4f18cf645 {n : Type*} [Fintype n] [DecidableEq n]
    {G G' : Matrix n n ℂ} (hG : G.PosDef) (hG' : G'.PosSemidef) (c : ℝ)
    (hc : (c • G - G').PosSemidef) : (det G').re ≤ c ^ Fintype.card n * (det G).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«re_det_le_of_posSemidef_smul_sub» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_le_of_posSemidef_smul_sub_78b4f18cf645
