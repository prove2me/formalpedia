-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_embForm_ne_C_ab4f1ef91293
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_embForm_ne_C_ab4f1ef91293
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:25.057808+00:00
-- url     : https://prove2.me/theorems/14be9c99-978c-52dc-83c1-f19edc1a1d68
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible emb Form ne C ab4f1ef91293: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible emb Form ne C ab4f1ef91293
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible emb Form ne C ab4f1ef91293 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible emb Form ne C ab4f1ef91293 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L196-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L196-L205

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_embForm_ne_C_ab4f1ef91293 (σ : L →ₐ[E] K) (ht : ∑ j, algebraMap E L (t j) * x j = 1) (r : K) :
    embForm σ x ≠ C r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«embForm_ne_C» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_embForm_ne_C_ab4f1ef91293
