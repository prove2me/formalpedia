-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_solve_inr_ae6d804b71ce
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_solve_inr_ae6d804b71ce
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:28.349817+00:00
-- url     : https://prove2.me/theorems/27b0d784-3c7c-5f6e-b330-55478fd3d3c8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart solve inr ae6d804b71ce: P2 M Ground Theory Heights  Heights Vertical Spec Chart solve inr ae6d804b71ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart solve inr ae6d804b71ce construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart solve inr ae6d804b71ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L20-L22

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_solve_inr_ae6d804b71ce {L : Type*} [CommRing L] {u x ci S : L} (h : u * x + S = 1) (hc : ci * x = 1) :
    ci * (1 - S) = u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«solve_inr» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_solve_inr_ae6d804b71ce
