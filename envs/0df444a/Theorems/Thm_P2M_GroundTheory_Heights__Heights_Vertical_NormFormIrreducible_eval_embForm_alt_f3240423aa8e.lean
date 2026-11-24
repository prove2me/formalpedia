-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_alt_f3240423aa8e
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_alt_f3240423aa8e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:34.172808+00:00
-- url     : https://prove2.me/theorems/b2a30de8-e48d-4b7c-a4ce-6f5dec533e2e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eval emb Form alt f3240423aa8e: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eval emb Form alt f3240423aa8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eval emb Form alt f3240423aa8e construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eval emb Form alt f3240423aa8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L190-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L190-L194

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_alt_f3240423aa8e (σ : L →ₐ[E] K) (ht : ∑ j, algebraMap E L (t j) * x j = 1) :
    eval (fun j => algebraMap E K (t j)) (embForm σ x) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«eval_embForm_alt» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_alt_f3240423aa8e
