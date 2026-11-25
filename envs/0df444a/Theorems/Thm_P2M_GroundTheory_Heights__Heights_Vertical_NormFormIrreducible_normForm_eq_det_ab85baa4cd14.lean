-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_eq_det_ab85baa4cd14
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_eq_det_ab85baa4cd14
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:39.333638+00:00
-- url     : https://prove2.me/theorems/b5490782-a272-4532-9d7f-393469116771
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible norm Form eq det ab85baa4cd14: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible norm Form eq det ab85baa4cd14
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible norm Form eq det ab85baa4cd14 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible norm Form eq det ab85baa4cd14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L55-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L55-L85

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_eq_det_ab85baa4cd14 {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (x : Fin n → A) :
    normForm A x = (∑ j, (X j : MvPolynomial (Fin n) R) • (Algebra.leftMulMatrix b (x j)).map C).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«normForm_eq_det» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_eq_det_ab85baa4cd14
