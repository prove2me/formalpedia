-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_repr_symm_bee5a38d5919
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_repr_symm_bee5a38d5919
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:11.475919+00:00
-- url     : https://prove2.me/theorems/b07216db-5c60-419d-81f8-8cbd78667cd1
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms apply repr symm bee5a38d5919: P2 M Ground Theory Heights  Heights Fibre Mahler Forms apply repr symm bee5a38d5919
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms apply repr symm bee5a38d5919 construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms apply repr symm bee5a38d5919 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_repr_symm_bee5a38d5919 (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ℓ (b.repr.symm (WithLp.toLp 2 v)) = ∑ j, ℓ (b j) * v j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«apply_repr_symm» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_repr_symm_bee5a38d5919
