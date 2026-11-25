-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalAlg_TowerSq_thickTrans_thick__1d9f45897eeb
-- name    : P2M_GlobalTheory_FormalAlg_TowerSq_thickTrans_thick__1d9f45897eeb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:14.260477+00:00
-- url     : https://prove2.me/theorems/2d51a47b-aae8-4904-a1f8-28bdb543a64b
-- title:
--   P2 M Global Theory Formal Alg Tower Sq thick Trans thick  1d9f45897eeb: P2 M Global Theory Formal Alg Tower Sq thick Trans thick  1d9f45897eeb
-- statement:
--   The P2 M Global Theory Formal Alg Tower Sq thick Trans thick  1d9f45897eeb construction uses the P2 M Global Theory Formal Alg Tower Sq thick Trans thick  1d9f45897eeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TowerSquares.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TowerSquares.lean#L27-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TowerSquares
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FormalAlg GlobalTheory.FormalAlg.TowerSq

theorem P2M_GlobalTheory_FormalAlg_TowerSq_thickTrans_thick__1d9f45897eeb (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    thickTrans R I e ≫ thick R I (e + 1) = thick R I e := by sorry

alias «GlobalTheory».«FormalAlg».«TowerSq».«thickTrans_thick'» := P2M_GlobalTheory_FormalAlg_TowerSq_thickTrans_thick__1d9f45897eeb
