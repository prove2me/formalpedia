-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_0569ab2071d7
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_0569ab2071d7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:28.07146+00:00
-- url     : https://prove2.me/theorems/96e73b8d-3f31-5f0c-9794-174ff524bbb4
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas re det gram le prod 0569ab2071d7: P2 M Ground Theory Heights  Heights Lattice Lemmas re det gram le prod 0569ab2071d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas re det gram le prod 0569ab2071d7 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas re det gram le prod 0569ab2071d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean#L48-L54

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_0569ab2071d7 {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → V) :
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«re_det_gram_le_prod» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_0569ab2071d7
