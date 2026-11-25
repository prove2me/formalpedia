-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_fibreGen_surjective_dc495228befe
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_fibreGen_surjective_dc495228befe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:31.884193+00:00
-- url     : https://prove2.me/theorems/56a367c4-7190-507f-b23e-a915c2dc7e0c
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms fibre Gen surjective dc495228befe: P2 M Ground Theory Heights  Heights Fibre Mahler Forms fibre Gen surjective dc495228befe
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms fibre Gen surjective dc495228befe construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms fibre Gen surjective dc495228befe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L144-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L144-L165

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

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_fibreGen_surjective_dc495228befe (h : HermitianMetric F W) (σ : F →+* ℂ) {n : ℕ} (w : Fin n → W)
    (hw : Submodule.span (𝓞 F) (Set.range w) = ⊤) : Function.Surjective (fibreGen h σ w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«fibreGen_surjective» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_fibreGen_surjective_dc495228befe
