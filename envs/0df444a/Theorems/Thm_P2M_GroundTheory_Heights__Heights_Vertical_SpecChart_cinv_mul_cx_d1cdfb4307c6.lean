-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_cinv_mul_cx_d1cdfb4307c6
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_cinv_mul_cx_d1cdfb4307c6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:18.385796+00:00
-- url     : https://prove2.me/theorems/21fe7ec1-11a8-4709-b5c8-496a14fc8545
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart cinv mul cx d1cdfb4307c6: P2 M Ground Theory Heights  Heights Vertical Spec Chart cinv mul cx d1cdfb4307c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart cinv mul cx d1cdfb4307c6 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart cinv mul cx d1cdfb4307c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L44-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_cinv_mul_cx_d1cdfb4307c6 : cinv e I j * cx e I j j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«cinv_mul_cx» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_cinv_mul_cx_d1cdfb4307c6
