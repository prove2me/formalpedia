-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archDualNorm_eq_5570a2d01de9
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archDualNorm_eq_5570a2d01de9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:58.265541+00:00
-- url     : https://prove2.me/theorems/04ada89a-14ba-45bb-be5b-576da4c46d47
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Dual Norm eq 5570a2d01de9: P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Dual Norm eq 5570a2d01de9
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Dual Norm eq 5570a2d01de9 construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Dual Norm eq 5570a2d01de9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L196-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L196-L199

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
variable {K : Type} [Field K] [NumberField K] [Algebra F K]

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archDualNorm_eq_5570a2d01de9 (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℂ (FibreSpace h (τ.comp (algebraMap F K)))) :
    archDualNorm h τ yv = √(∑ j, ‖archLin h τ yv (b j)‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«archDualNorm_eq» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archDualNorm_eq_5570a2d01de9
