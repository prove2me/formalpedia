-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_eq_sum_1364e9b5a1d6
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_eq_sum_1364e9b5a1d6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:50.671885+00:00
-- url     : https://prove2.me/theorems/2a51735c-c566-5df6-b4c0-ea254ee14d4f
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms apply eq sum 1364e9b5a1d6: P2 M Ground Theory Heights  Heights Fibre Mahler Forms apply eq sum 1364e9b5a1d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms apply eq sum 1364e9b5a1d6 construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms apply eq sum 1364e9b5a1d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L21-L24

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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_eq_sum_1364e9b5a1d6 (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (ξ : V) :
    ℓ ξ = ∑ j, inner ℂ (b j) ξ * ℓ (b j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«apply_eq_sum» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_eq_sum_1364e9b5a1d6
