-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMatrix_rows_ddb0ef3043fc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMatrix_rows_ddb0ef3043fc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:59.089606+00:00
-- url     : https://prove2.me/theorems/2199aa52-f60f-53a7-92e3-e5aaf584039d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Matrix rows ddb0ef3043fc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Fl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Matrix rows ddb0ef3043fc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Matrix rows ddb0ef3043fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotIdentity.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotIdentity.lean#L48-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotIdentity
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
variable {R : Type} [CommRing R] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMatrix_rows_ddb0ef3043fc (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) {m : ℕ} (e : Fin m → Fin n) :
    (pivotMatrix M).submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e =
      pivotCoeff M j * M.submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagPivotIdentity».«pivotMatrix_rows» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMatrix_rows_ddb0ef3043fc
