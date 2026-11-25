-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finrank_eq_e3e2ee841f1e
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finrank_eq_e3e2ee841f1e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:45.309209+00:00
-- url     : https://prove2.me/theorems/fc268e61-2507-48ca-86e9-6915946d8882
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts finrank eq e3e2ee841f1e: P2 M Ground Theory Heights  Heights Curve Affine Charts finrank eq e3e2ee841f1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts finrank eq e3e2ee841f1e construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts finrank eq e3e2ee841f1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L148-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L148-L177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finrank_eq_e3e2ee841f1e [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) :
    Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«finrank_eq» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finrank_eq_e3e2ee841f1e
