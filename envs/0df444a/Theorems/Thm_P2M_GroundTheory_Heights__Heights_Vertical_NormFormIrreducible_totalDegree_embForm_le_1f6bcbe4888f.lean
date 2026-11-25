-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_totalDegree_embForm_le_1f6bcbe4888f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_totalDegree_embForm_le_1f6bcbe4888f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:05.789942+00:00
-- url     : https://prove2.me/theorems/6d5814b5-d1ab-45f8-a29c-a2c0437178d6
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible total Degree emb Form le 1f6bcbe4888f: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible total Degree emb Form le 1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible total Degree emb Form le 1f6bcbe4888f construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible total Degree emb Form le 1f6bcbe4888f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L185-L188

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_totalDegree_embForm_le_1f6bcbe4888f (σ : L →ₐ[E] K) (x : Fin n → L) : (embForm σ x).totalDegree ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«totalDegree_embForm_le» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_totalDegree_embForm_le_1f6bcbe4888f
