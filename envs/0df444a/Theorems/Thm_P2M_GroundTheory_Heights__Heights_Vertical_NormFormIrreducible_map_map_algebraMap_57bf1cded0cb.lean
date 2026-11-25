-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_map_algebraMap_57bf1cded0cb
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_map_algebraMap_57bf1cded0cb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:44:11.930985+00:00
-- url     : https://prove2.me/theorems/2c416f73-42dc-5c10-ac7e-6a7ad9522ddb
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible map map algebra Map 57bf1cded0cb: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible map map algebra Map 57bf1cded0cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible map map algebra Map 57bf1cded0cb construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible map map algebra Map 57bf1cded0cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L251-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L251-L253

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_map_algebraMap_57bf1cded0cb (τ : K →ₐ[E] K) (p : MvPolynomial (Fin n) E) :
    (p.map (algebraMap E K)).map (τ : K →+* K) = p.map (algebraMap E K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«map_map_algebraMap» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_map_algebraMap_57bf1cded0cb
