-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_det_submatrix_sign_ed8aebb8ad35
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_det_submatrix_sign_ed8aebb8ad35
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:07.384824+00:00
-- url     : https://prove2.me/theorems/d513ef3f-4c03-5b26-bbde-a316fdad9edc
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety det submatrix sign ed8aebb8ad35: P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety det submatrix sign ed8aebb8ad35
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety det submatrix sign ed8aebb8ad35 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety det submatrix sign ed8aebb8ad35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassArithVar.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassArithVar.lean#L13-L25

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_det_submatrix_sign_ed8aebb8ad35 {R : Type*} [CommRing R] {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (g h : Fin j → Fin N) (hg : Function.Injective g) (hh : Function.Injective h)
    (hr : Set.range h = Set.range g) :
    ∃ s : ℤˣ, (A.submatrix id h).det = ((s : ℤ) : R) * (A.submatrix id g).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianArithmeticVariety».«det_submatrix_sign» := P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_det_submatrix_sign_ed8aebb8ad35
