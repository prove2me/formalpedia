-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_exists_mul_eq_one_a97e11134c8a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_exists_mul_eq_one_a97e11134c8a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:46:51.16126+00:00
-- url     : https://prove2.me/theorems/be68efac-1977-588c-b468-da91d797fbff
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Minors Base Change exists mul eq one a97e11134c8a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inte
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Minors Base Change exists mul eq one a97e11134c8a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Minors Base Change exists mul eq one a97e11134c8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsBaseChange.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsBaseChange.lean#L41-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsBaseChange
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMinorsBaseChange

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_exists_mul_eq_one_a97e11134c8a {F : Type} [Field F] {n N1 : ℕ} (B : Matrix (Fin n) (Fin N1) F)
    (hB : LinearIndependent F B) : ∃ D : Matrix (Fin N1) (Fin n) F, B * D = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagMinorsBaseChange».«exists_mul_eq_one» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_exists_mul_eq_one_a97e11134c8a
