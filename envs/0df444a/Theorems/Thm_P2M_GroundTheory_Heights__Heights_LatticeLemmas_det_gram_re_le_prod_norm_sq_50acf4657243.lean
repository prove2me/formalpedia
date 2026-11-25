-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_gram_re_le_prod_norm_sq_50acf4657243
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_gram_re_le_prod_norm_sq_50acf4657243
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:33:20.770086+00:00
-- url     : https://prove2.me/theorems/d6bfc9a9-6202-5822-a731-9d9c9f085333
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas det gram re le prod norm sq 50acf4657243: P2 M Ground Theory Heights  Heights Lattice Lemmas det gram re le prod norm sq 50acf4657243
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas det gram re le prod norm sq 50acf4657243 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas det gram re le prod norm sq 50acf4657243 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamard.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamard.lean#L14-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamard
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
open GroundTheory.Heights₂.Heights InnerProductSpace
universe u v w
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_gram_re_le_prod_norm_sq_50acf4657243 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) :
    (det (gram ℂ v)).re ≤ ∏ i, ‖v i‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«det_gram_re_le_prod_norm_sq» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_gram_re_le_prod_norm_sq_50acf4657243
