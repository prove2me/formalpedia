-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_exists_comp_eq_b7eb0fc85b9b
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_exists_comp_eq_b7eb0fc85b9b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:44:04.793836+00:00
-- url     : https://prove2.me/theorems/e4febd6c-09db-5962-9087-8d4803ed1f21
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible exists comp eq b7eb0fc85b9b: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible exists comp eq b7eb0fc85b9b
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible exists comp eq b7eb0fc85b9b construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible exists comp eq b7eb0fc85b9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L255-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L255-L262

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_exists_comp_eq_b7eb0fc85b9b [FiniteDimensional E L] [Algebra.IsSeparable E L] [IsAlgClosed K]
    [Algebra.IsAlgebraic E K] (σ σ' : L →ₐ[E] K) : ∃ τ : K →ₐ[E] K, τ.comp σ = σ' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«exists_comp_eq» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_exists_comp_eq_b7eb0fc85b9b
