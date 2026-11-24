-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_map_ofReal_88bce7305c00
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_map_ofReal_88bce7305c00
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:47.027269+00:00
-- url     : https://prove2.me/theorems/5dd07245-f196-4662-9a4c-6b097d8a8af5
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds pos Semidef map of Real 88bce7305c00: P2 M Ground Theory Heights  Heights MCBounds pos Semidef map of Real 88bce7305c00
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds pos Semidef map of Real 88bce7305c00 construction uses the P2 M Ground Theory Heights  Heights MCBounds pos Semidef map of Real 88bce7305c00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L157-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L157-L186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section
open scoped ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_map_ofReal_88bce7305c00 {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (A.map (fun x : ℝ => (x : ℂ))).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«posSemidef_map_ofReal» := P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_map_ofReal_88bce7305c00
