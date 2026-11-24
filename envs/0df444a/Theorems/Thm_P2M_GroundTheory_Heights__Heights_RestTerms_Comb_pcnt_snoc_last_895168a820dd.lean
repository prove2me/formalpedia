-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_snoc_last_895168a820dd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_snoc_last_895168a820dd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:37.04192+00:00
-- url     : https://prove2.me/theorems/58850fb9-a0ad-4e27-b16c-9ebd6e26a5d9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt snoc last 895168a820dd: P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt snoc last 895168a820dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt snoc last 895168a820dd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt snoc last 895168a820dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L32-L41

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_snoc_last_895168a820dd {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) (n + 1) i = pcnt w n i + if a = i then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«pcnt_snoc_last» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_snoc_last_895168a820dd
