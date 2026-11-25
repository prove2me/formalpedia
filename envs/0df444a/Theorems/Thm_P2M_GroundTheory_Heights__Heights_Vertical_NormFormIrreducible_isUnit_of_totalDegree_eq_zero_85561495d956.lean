-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_totalDegree_eq_zero_85561495d956
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_totalDegree_eq_zero_85561495d956
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:37.73465+00:00
-- url     : https://prove2.me/theorems/5a01b1fd-de6e-5c63-840d-cad18fa29a59
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible is Unit of total Degree eq zero 85561495d956: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible is Unit of total Deg
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible is Unit of total Degree eq zero 85561495d956 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible is Unit of total Degree eq zero 85561495d956 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L156-L160

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
variable {K : Type*} [Field K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_totalDegree_eq_zero_85561495d956 {p : MvPolynomial (Fin n) K} (hp : p ≠ 0)
    (hd : p.totalDegree = 0) : IsUnit p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«isUnit_of_totalDegree_eq_zero» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_totalDegree_eq_zero_85561495d956
