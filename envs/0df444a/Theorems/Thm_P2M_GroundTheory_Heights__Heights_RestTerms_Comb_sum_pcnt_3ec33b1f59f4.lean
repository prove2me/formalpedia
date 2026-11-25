-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sum_pcnt_3ec33b1f59f4
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sum_pcnt_3ec33b1f59f4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:09.317964+00:00
-- url     : https://prove2.me/theorems/d7bcbed3-5254-5f50-a547-3ee161163266
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb sum pcnt 3ec33b1f59f4: P2 M Ground Theory Heights  Heights Rest Terms Comb sum pcnt 3ec33b1f59f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb sum pcnt 3ec33b1f59f4 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb sum pcnt 3ec33b1f59f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L51-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
open scoped Classical
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sum_pcnt_3ec33b1f59f4 {n : ℕ} (w : Fin n → Fin m) : ∑ i, pcnt w n i = n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«sum_pcnt» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sum_pcnt_3ec33b1f59f4
