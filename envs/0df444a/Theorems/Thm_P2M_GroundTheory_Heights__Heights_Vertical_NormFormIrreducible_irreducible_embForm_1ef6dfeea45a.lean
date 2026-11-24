-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_embForm_1ef6dfeea45a
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_embForm_1ef6dfeea45a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:58.003871+00:00
-- url     : https://prove2.me/theorems/731eac86-0a00-4ec1-a825-7ce7fd315f56
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible irreducible emb Form 1ef6dfeea45a: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible irreducible emb Form 1ef6dfeea4
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible irreducible emb Form 1ef6dfeea45a construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible irreducible emb Form 1ef6dfeea45a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L207-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L207-L209

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_embForm_1ef6dfeea45a (σ : L →ₐ[E] K) (ht : ∑ j, algebraMap E L (t j) * x j = 1) :
    Irreducible (embForm σ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«irreducible_embForm» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_embForm_1ef6dfeea45a
