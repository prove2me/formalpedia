-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_update_pred_sub_9997e7a05bb7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_update_pred_sub_9997e7a05bb7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:27.097667+00:00
-- url     : https://prove2.me/theorems/38b9375b-1a9a-493a-b811-bcace9ec422f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb update pred sub 9997e7a05bb7: P2 M Ground Theory Heights  Heights Rest Terms Comb update pred sub 9997e7a05bb7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb update pred sub 9997e7a05bb7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb update pred sub 9997e7a05bb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L63-L67

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_update_pred_sub_9997e7a05bb7 (lam : Fin m → ℕ) (a i : Fin m) (h : 1 ≤ lam a) :
    Function.update lam a (lam a - 1) i + (if a = i then 1 else 0) = lam i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«update_pred_sub» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_update_pred_sub_9997e7a05bb7
