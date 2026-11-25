-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_fin_5585265ad779
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_fin_5585265ad779
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:35.506627+00:00
-- url     : https://prove2.me/theorems/f8e34cc4-c01e-5bb6-9f3e-d170014bfcae
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas re det gram le prod fin 5585265ad779: P2 M Ground Theory Heights  Heights Lattice Lemmas re det gram le prod fin 5585265ad779
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas re det gram le prod fin 5585265ad779 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas re det gram le prod fin 5585265ad779 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean#L24-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean#L24-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean
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
open NumberField Matrix GroundTheory.Heights₂.Heights
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_fin_5585265ad779 : ∀ (n : ℕ) (c : Fin n → V),
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«re_det_gram_le_prod_fin» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_fin_5585265ad779
