-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_embForm_6c2c91246726
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_embForm_6c2c91246726
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:57.993019+00:00
-- url     : https://prove2.me/theorems/fbc27a6e-c8c7-4492-9db1-ca78c2fcd427
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible map emb Form 6c2c91246726: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible map emb Form 6c2c91246726
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible map emb Form 6c2c91246726 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible map emb Form 6c2c91246726 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L247-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L247-L249

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_embForm_6c2c91246726 (τ : K →ₐ[E] K) (σ : L →ₐ[E] K) :
    (embForm σ x).map (τ : K →+* K) = embForm (τ.comp σ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«map_embForm» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_embForm_6c2c91246726
