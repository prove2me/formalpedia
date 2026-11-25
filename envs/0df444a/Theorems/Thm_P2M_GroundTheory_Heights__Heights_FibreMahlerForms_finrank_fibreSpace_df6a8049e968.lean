-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_finrank_fibreSpace_df6a8049e968
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_finrank_fibreSpace_df6a8049e968
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:09.889122+00:00
-- url     : https://prove2.me/theorems/f92a8508-ee4b-5e26-b28f-6af59d9ecd26
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms finrank fibre Space df6a8049e968: P2 M Ground Theory Heights  Heights Fibre Mahler Forms finrank fibre Space df6a8049e968
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms finrank fibre Space df6a8049e968 construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms finrank fibre Space df6a8049e968 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L137-L142

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
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
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (𝓞 F) W]
  [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_finrank_fibreSpace_df6a8049e968 (h : HermitianMetric F W) (σ : F →+* ℂ) :
    Module.finrank ℂ (FibreSpace h σ) = Module.finrank (𝓞 F) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«finrank_fibreSpace» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_finrank_fibreSpace_df6a8049e968
