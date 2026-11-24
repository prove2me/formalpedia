-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_mem_conePts_bot_8cd7c8de083b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_mem_conePts_bot_8cd7c8de083b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:25:15.403346+00:00
-- url     : https://prove2.me/theorems/ef908869-e6d2-4692-9604-95b03bddc426
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout mem cone Pts bot 8cd7c8de083b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout mem cone
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout mem cone Pts bot 8cd7c8de083b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout mem cone Pts bot 8cd7c8de083b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L175-L177

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_mem_conePts_bot_8cd7c8de083b {n : ℕ} (z : Fin n → ℂ) :
    z ∈ conePts (Int.castRingHom ℂ) (⊥ : Ideal (MvPolynomial (Fin n) ℤ)) ↔ z ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ArithBezout».«mem_conePts_bot» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_mem_conePts_bot_8cd7c8de083b
