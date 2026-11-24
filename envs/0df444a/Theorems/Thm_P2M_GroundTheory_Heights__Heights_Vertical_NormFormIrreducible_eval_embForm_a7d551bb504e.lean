-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_a7d551bb504e
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_a7d551bb504e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:11.887182+00:00
-- url     : https://prove2.me/theorems/c507d5ec-2bac-4a1e-91d6-8f473564e612
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eval emb Form a7d551bb504e: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eval emb Form a7d551bb504e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eval emb Form a7d551bb504e construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eval emb Form a7d551bb504e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L94-L96

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_a7d551bb504e (σ : L →ₐ[E] K) (x : Fin n → L) (u : Fin n → K) :
    eval u (embForm σ x) = ∑ j, u j * σ (x j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«eval_embForm» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_a7d551bb504e
