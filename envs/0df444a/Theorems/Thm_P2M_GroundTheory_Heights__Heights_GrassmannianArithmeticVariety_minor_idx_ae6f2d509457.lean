-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_minor_idx_ae6f2d509457
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_minor_idx_ae6f2d509457
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:09.461461+00:00
-- url     : https://prove2.me/theorems/a0a6c409-59a2-47e6-afa4-9d5f0afeab1e
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety minor idx ae6f2d509457: P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety minor idx ae6f2d509457
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety minor idx ae6f2d509457 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Arithmetic Variety minor idx ae6f2d509457 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassArithVar.lean#L42-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassArithVar.lean#L42-L56

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_minor_idx_ae6f2d509457 {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R)
    (a : Fin j) (b : Fin m) :
    ∃ s : ℤˣ, (colsOf (onePipe Z) (idx a b)).det = ((s : ℤ) : R) * Z a b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianArithmeticVariety».«minor_idx» := P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_minor_idx_ae6f2d509457
