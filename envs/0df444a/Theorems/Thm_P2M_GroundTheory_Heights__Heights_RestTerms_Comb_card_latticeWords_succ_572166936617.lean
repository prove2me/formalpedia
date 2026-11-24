-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_card_latticeWords_succ_572166936617
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_card_latticeWords_succ_572166936617
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:50.011423+00:00
-- url     : https://prove2.me/theorems/f2b952e5-8393-4256-9028-50561776f0e9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb card lattice Words succ 572166936617: P2 M Ground Theory Heights  Heights Rest Terms Comb card lattice Words succ 572166936617
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb card lattice Words succ 572166936617 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb card lattice Words succ 572166936617 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L69-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L69-L114

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_card_latticeWords_succ_572166936617 (n : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (latticeWords (n + 1) lam).card =
      ∑ a : Fin m, if 1 ≤ lam a then (latticeWords n (Function.update lam a (lam a - 1))).card else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«card_latticeWords_succ» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_card_latticeWords_succ_572166936617
