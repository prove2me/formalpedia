-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_anchor_minor_b307d35ccb1e
-- name    : P2M_GroundTheory_Heights__Heights_anchor_minor_b307d35ccb1e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:33.418664+00:00
-- url     : https://prove2.me/theorems/1a61e413-db5f-444a-b5d7-a3f4d125a2be
-- title:
--   P2 M Ground Theory Heights  Heights anchor minor b307d35ccb1e: P2 M Ground Theory Heights  Heights anchor minor b307d35ccb1e
-- statement:
--   The P2 M Ground Theory Heights  Heights anchor minor b307d35ccb1e construction uses the P2 M Ground Theory Heights  Heights anchor minor b307d35ccb1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGrassHeightNE.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGrassHeightNE.lean#L20-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_anchor_minor_b307d35ccb1e {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«anchor_minor» := P2M_GroundTheory_Heights__Heights_anchor_minor_b307d35ccb1e
