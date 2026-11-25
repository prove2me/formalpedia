-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreVec_3b5dbbaf6e5b
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreVec_3b5dbbaf6e5b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:02.58994+00:00
-- url     : https://prove2.me/theorems/4179d891-79c0-5ff3-9b3b-433bffcef5b3
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Lin fibre Vec 3b5dbbaf6e5b: P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Lin fibre Vec 3b5dbbaf6e5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Lin fibre Vec 3b5dbbaf6e5b construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms arch Lin fibre Vec 3b5dbbaf6e5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L185-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L185-L189

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

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreVec_3b5dbbaf6e5b (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (e : W) :
    archLin h τ yv (fibreVec h (τ.comp (algebraMap F K)) e) = τ (yv e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«archLin_fibreVec» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreVec_3b5dbbaf6e5b
