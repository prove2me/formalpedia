-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotCoeff_diag_fb5ec8ecbf02
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotCoeff_diag_fb5ec8ecbf02
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:06.815493+00:00
-- url     : https://prove2.me/theorems/368acbe3-a642-50f5-af42-e11eaa51f761
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Coeff diag fb5ec8ecbf02: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Fla
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Coeff diag fb5ec8ecbf02 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Coeff diag fb5ec8ecbf02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotIdentity.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotIdentity.lean#L75-L81

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotCoeff_diag_fb5ec8ecbf02 (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (a : Fin (j + 1)) :
    pivotCoeff M j a a = leadDet M a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagPivotIdentity».«pivotCoeff_diag» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotCoeff_diag_fb5ec8ecbf02
