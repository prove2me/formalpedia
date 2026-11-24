-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_normForm_eq_det_40a80ca110c3
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_normForm_eq_det_40a80ca110c3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:20.54644+00:00
-- url     : https://prove2.me/theorems/cd1bf20a-5cfe-4db1-8cd4-615e69086be5
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change norm Form eq det 40a80ca110c3: P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change norm Form eq det 40a80ca110c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change norm Form eq det 40a80ca110c3 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change norm Form eq det 40a80ca110c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFieldChange.lean#L14-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFieldChange.lean#L14-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
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
open MvPolynomial
open scoped TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_normForm_eq_det_40a80ca110c3 {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) {n : ℕ} (x : Fin n → A) :
    normForm A x = Matrix.det (Matrix.of fun i k => ∑ j, X j * C (b.repr (x j * b k) i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecAlgFieldChange».«normForm_eq_det» := P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_normForm_eq_det_40a80ca110c3
