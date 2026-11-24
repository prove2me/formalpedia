-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_latticeWords_eq_empty_of_not_antitone_43d03e7e6eb5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_latticeWords_eq_empty_of_not_antitone_43d03e7e6eb5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:58.026853+00:00
-- url     : https://prove2.me/theorems/b8d8afb2-93e2-43b7-a53b-c1649c280a06
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb lattice Words eq empty of not antitone 43d03e7e6eb5: P2 M Ground Theory Heights  Heights Rest Terms Comb lattice Words eq empty of not antitone 43d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb lattice Words eq empty of not antitone 43d03e7e6eb5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb lattice Words eq empty of not antitone 43d03e7e6eb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L125-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L125-L133

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_latticeWords_eq_empty_of_not_antitone_43d03e7e6eb5 (n : ℕ) (lam : Fin m → ℕ) (h : ¬ Antitone lam) :
    latticeWords n lam = ∅ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«latticeWords_eq_empty_of_not_antitone» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_latticeWords_eq_empty_of_not_antitone_43d03e7e6eb5
