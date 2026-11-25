-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_zero_330963990738
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_zero_330963990738
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:55.853094+00:00
-- url     : https://prove2.me/theorems/ceaaa301-eb9a-4d75-b0e1-e522d83899c3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt zero 330963990738: P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt zero 330963990738
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt zero 330963990738 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt zero 330963990738 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L43-L44

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_zero_330963990738 {n : ℕ} (w : Fin n → Fin m) (i : Fin m) : pcnt w 0 i = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«pcnt_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_zero_330963990738
