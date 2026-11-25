-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_normForm_eq_det_0ca3f0e920b9
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_normForm_eq_det_0ca3f0e920b9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:29.193922+00:00
-- url     : https://prove2.me/theorems/3ce84b85-371f-4b3d-9add-79fd78f47808
-- title:
--   P2 M Ground Theory Heights  Heights Vertical norm Form eq det 0ca3f0e920b9: P2 M Ground Theory Heights  Heights Vertical norm Form eq det 0ca3f0e920b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical norm Form eq det 0ca3f0e920b9 construction uses the P2 M Ground Theory Heights  Heights Vertical norm Form eq det 0ca3f0e920b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormEval.lean#L53-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormEval.lean#L53-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
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
open MvPolynomial TensorProduct
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem P2M_GroundTheory_Heights__Heights_Vertical_normForm_eq_det_0ca3f0e920b9 {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (x : Fin n → A) :
    normForm A x = (∑ j, (X j : MvPolynomial (Fin n) R) • (Algebra.leftMulMatrix b (x j)).map C).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«normForm_eq_det» := P2M_GroundTheory_Heights__Heights_Vertical_normForm_eq_det_0ca3f0e920b9
