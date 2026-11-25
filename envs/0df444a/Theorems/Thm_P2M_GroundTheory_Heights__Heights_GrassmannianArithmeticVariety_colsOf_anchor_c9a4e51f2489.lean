-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_colsOf_anchor_c9a4e51f2489
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_colsOf_anchor_c9a4e51f2489
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:04.211363+00:00
-- url     : https://prove2.me/theorems/b6599cd3-276f-4317-b21b-39908ffe8dbe
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety cols Of anchor c9a4e51f2489: P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety cols Of anchor c9a4e51f2489
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety cols Of anchor c9a4e51f2489 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety cols Of anchor c9a4e51f2489 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassArithVar.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassArithVar.lean#L58-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassArithVar
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
open GroundTheory.Heights₂.Heights.GrassmannianArithmeticVariety

theorem P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_colsOf_anchor_c9a4e51f2489 {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    colsOf (onePipe Z) (plAnchor j m) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianArithmeticVariety».«colsOf_anchor» := P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_colsOf_anchor_c9a4e51f2489
