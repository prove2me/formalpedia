-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_exists_archLin_ne_zero_ed53fe7598d6
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_exists_archLin_ne_zero_ed53fe7598d6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:23.164627+00:00
-- url     : https://prove2.me/theorems/adec56fe-66e1-5559-95dd-5e93b59badf0
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms exists arch Lin ne zero ed53fe7598d6: P2 M Ground Theory Heights  Heights Fibre Mahler Forms exists arch Lin ne zero ed53fe7598d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms exists arch Lin ne zero ed53fe7598d6 construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms exists arch Lin ne zero ed53fe7598d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L201-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L201-L214

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

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_exists_archLin_ne_zero_ed53fe7598d6 (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K)
    (hy : yv ≠ 0) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (FibreSpace h (τ.comp (algebraMap F K)))) :
    ∃ j, archLin h τ yv (b j) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«exists_archLin_ne_zero» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_exists_archLin_ne_zero_ed53fe7598d6
