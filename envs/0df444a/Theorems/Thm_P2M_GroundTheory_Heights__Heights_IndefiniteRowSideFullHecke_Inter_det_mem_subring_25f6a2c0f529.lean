-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_mem_subring_25f6a2c0f529
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_mem_subring_25f6a2c0f529
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:21:35.876918+00:00
-- url     : https://prove2.me/theorems/c90856c2-ea14-5693-a75d-35739e25f103
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter det mem subring 25f6a2c0f529: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter det mem subring 25f6a2c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter det mem subring 25f6a2c0f529 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter det mem subring 25f6a2c0f529 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L42-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_mem_subring_25f6a2c0f529 {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] (S : Subring R)
    (M : Matrix m m R) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«det_mem_subring» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_mem_subring_25f6a2c0f529
