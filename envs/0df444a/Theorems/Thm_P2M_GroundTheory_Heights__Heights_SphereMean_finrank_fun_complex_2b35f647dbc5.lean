-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_finrank_fun_complex_2b35f647dbc5
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_finrank_fun_complex_2b35f647dbc5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:28.972019+00:00
-- url     : https://prove2.me/theorems/a7e7adfe-6f76-4d9c-9e63-b0dbede69da6
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean finrank fun complex 2b35f647dbc5: P2 M Ground Theory Heights  Heights Sphere Mean finrank fun complex 2b35f647dbc5
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean finrank fun complex 2b35f647dbc5 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean finrank fun complex 2b35f647dbc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L78-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_finrank_fun_complex_2b35f647dbc5 (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«finrank_fun_complex» := P2M_GroundTheory_Heights__Heights_SphereMean_finrank_fun_complex_2b35f647dbc5
