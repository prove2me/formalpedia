-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_rowsPoly_9010d8778d16
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_eval_rowsPoly_9010d8778d16
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:25.890689+00:00
-- url     : https://prove2.me/theorems/9ee75c7a-f179-45e4-9d74-bb26a474a2f2
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets eval rows Poly 9010d8778d16: P2 M Ground Theory Heights  Heights Complex Sets eval rows Poly 9010d8778d16
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets eval rows Poly 9010d8778d16 construction uses the P2 M Ground Theory Heights  Heights Complex Sets eval rows Poly 9010d8778d16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericProjectionFinite.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericProjectionFinite.lean#L19-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_eval_rowsPoly_9010d8778d16 {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«eval_rowsPoly» := P2M_GroundTheory_Heights__Heights_ComplexSets_eval_rowsPoly_9010d8778d16
