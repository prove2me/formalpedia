-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreGen_25cb1cf05c25
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreGen_25cb1cf05c25
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:02.315103+00:00
-- url     : https://prove2.me/theorems/9507f469-312c-56f8-8772-f82149f6ccb6
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Lin fibre Gen 25cb1cf05c25: P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Lin fibre Gen 25cb1cf05c25
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Lin fibre Gen 25cb1cf05c25 construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Lin fibre Gen 25cb1cf05c25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L191-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L191-L194

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

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreGen_25cb1cf05c25 (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) {n : ℕ}
    (w : Fin n → W) (x : Fin n → ℂ) :
    archLin h τ yv (fibreGen h (τ.comp (algebraMap F K)) w x) = ∑ k, τ (yv (w k)) * x k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«archLin_fibreGen» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreGen_25cb1cf05c25
