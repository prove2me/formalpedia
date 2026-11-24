-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_zero_37c4884a24bb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_zero_37c4884a24bb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:48.284245+00:00
-- url     : https://prove2.me/theorems/a78e77a3-6073-4ebf-a878-3464448b69ac
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Minor eq zero 37c4884a24bb: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Minor eq zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Minor eq zero 37c4884a24bb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Minor eq zero 37c4884a24bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FlagPivot.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FlagPivot.lean#L46-L51

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_zero_37c4884a24bb {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hba : (b : ℕ) < a) : pivotMinor M a b = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«pivotMinor_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_zero_37c4884a24bb
