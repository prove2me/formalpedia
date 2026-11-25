-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_iSup_norm_ball_b20791a9192b
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_iSup_norm_ball_b20791a9192b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:10.645574+00:00
-- url     : https://prove2.me/theorems/0a324e09-949a-5355-8bdb-653cefe96f28
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms i Sup norm ball b20791a9192b: P2 M Ground Theory Heights  Heights Fibre Mahler Forms i Sup norm ball b20791a9192b
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms i Sup norm ball b20791a9192b construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms i Sup norm ball b20791a9192b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L31-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L31-L65

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

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_iSup_norm_ball_b20791a9192b (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) :
    ⨆ ξ : {ξ : V // ‖ξ‖ ≤ 1}, ‖ℓ ξ‖ = √(∑ j, ‖ℓ (b j)‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«iSup_norm_ball» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_iSup_norm_ball_b20791a9192b
