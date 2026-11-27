-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SgStarOddTheta_jacobiTheta__add_int_lattice_f9d485217309
-- name    : P2M_GlobalTheory_SgStarOddTheta_jacobiTheta__add_int_lattice_f9d485217309
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:36:43.190929+00:00
-- url     : https://prove2.me/theorems/40df23a4-a6e3-4d90-9a60-a1a122570fdf
-- title:
--   P2 M Global Theory Sg Star Odd Theta jacobi Theta  add int lattice f9d485217309: P2 M Global Theory Sg Star Odd Theta jacobi Theta  add int lattice f9d485217309
-- statement:
--   The P2 M Global Theory Sg Star Odd Theta jacobi Theta  add int lattice f9d485217309 construction uses the P2 M Global Theory Sg Star Odd Theta jacobi Theta  add int lattice f9d485217309 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/GaussianOddJacobiThetaEqDerivMulSgStar.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/GaussianOddJacobiThetaEqDerivMulSgStar.lean#L13-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open GlobalTheory GlobalTheory.SgStarOddTheta
open Formalism.L2.Th1.F

theorem P2M_GlobalTheory_SgStarOddTheta_jacobiTheta__add_int_lattice_f9d485217309 (z τ : ℂ) (m k : ℤ) :
    jacobiTheta₂ (z + (m * τ + k)) τ =
      cexp (-(Real.pi : ℂ) * I * (m ^ 2 * τ + 2 * m * z)) * jacobiTheta₂ z τ := by sorry

alias «GlobalTheory».«SgStarOddTheta».«jacobiTheta₂_add_int_lattice» := P2M_GlobalTheory_SgStarOddTheta_jacobiTheta__add_int_lattice_f9d485217309
