-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_mul_transpose_eq_one_d14d1218bc3d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_mul_transpose_eq_one_d14d1218bc3d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:16.329914+00:00
-- url     : https://prove2.me/theorems/3a1aae61-c521-57f1-8b39-27b5589e427b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists mul transpose eq one d14d1218bc3d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists mul t
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists mul transpose eq one d14d1218bc3d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists mul transpose eq one d14d1218bc3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleDim.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleDim.lean#L14-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleDim
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_mul_transpose_eq_one_d14d1218bc3d {F : Type} [Field F] {n N : ℕ} (B : Matrix (Fin n) (Fin N) F)
    (hB : LinearIndependent F B) : ∃ D : Matrix (Fin n) (Fin N) F, D * B.transpose = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«exists_mul_transpose_eq_one» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_mul_transpose_eq_one_d14d1218bc3d
