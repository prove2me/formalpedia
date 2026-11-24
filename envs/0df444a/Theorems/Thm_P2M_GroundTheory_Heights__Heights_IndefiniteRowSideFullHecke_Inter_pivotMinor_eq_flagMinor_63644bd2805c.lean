-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_flagMinor_63644bd2805c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_flagMinor_63644bd2805c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:54.915802+00:00
-- url     : https://prove2.me/theorems/57f6e523-cad6-4292-9184-35855af8e322
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Minor eq flag Minor 63644bd2805c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Minor eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Minor eq flag Minor 63644bd2805c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Minor eq flag Minor 63644bd2805c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FlagPivot.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FlagPivot.lean#L38-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagPivot
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_flagMinor_63644bd2805c {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hab : (a : ℕ) ≤ b) :
    pivotMinor M a b = flagMinor M a ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«pivotMinor_eq_flagMinor» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_flagMinor_63644bd2805c
