-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_castSucc_snoc_2f331b9c4057
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_castSucc_snoc_2f331b9c4057
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:03.257588+00:00
-- url     : https://prove2.me/theorems/ac892cd5-9276-43b2-b6d7-9d5d22da8b3b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt cast Succ snoc 2f331b9c4057: P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt cast Succ snoc 2f331b9c4057
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt cast Succ snoc 2f331b9c4057 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt cast Succ snoc 2f331b9c4057 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L25-L30

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_castSucc_snoc_2f331b9c4057 {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (t : ℕ) (ht : t ≤ n) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) t i = pcnt w t i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«pcnt_castSucc_snoc» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_castSucc_snoc_2f331b9c4057
