-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_map_isUnit_782e4226fb8b
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_map_isUnit_782e4226fb8b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:44:18.798159+00:00
-- url     : https://prove2.me/theorems/e60ea2f9-2b2b-42b8-96fb-9d58ec3fc79f
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible is Unit of map is Unit 782e4226fb8b: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible is Unit of map is Unit 782e42
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible is Unit of map is Unit 782e4226fb8b construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible is Unit of map is Unit 782e4226fb8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L264-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L264-L283

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_map_isUnit_782e4226fb8b {p : MvPolynomial (Fin n) E} (h : IsUnit (p.map (algebraMap E K))) :
    IsUnit p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«isUnit_of_map_isUnit» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_map_isUnit_782e4226fb8b
