-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMinor_eq_sum_d61a4d44f780
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMinor_eq_sum_d61a4d44f780
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:10.510811+00:00
-- url     : https://prove2.me/theorems/c6c85fee-b6da-58ea-a43d-340b440ac3a4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Minor eq sum d61a4d44f780: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter F
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Minor eq sum d61a4d44f780 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Identity pivot Minor eq sum d61a4d44f780 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotIdentity.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotIdentity.lean#L19-L32

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMinor_eq_sum_d61a4d44f780 (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) :
    pivotMinor M a b = ∑ i : Fin (a + 1),
      pivotCof M (a := a) (by have := a.2; omega) i * M (Fin.castLE (by have := a.2; omega) i) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagPivotIdentity».«pivotMinor_eq_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMinor_eq_sum_d61a4d44f780
