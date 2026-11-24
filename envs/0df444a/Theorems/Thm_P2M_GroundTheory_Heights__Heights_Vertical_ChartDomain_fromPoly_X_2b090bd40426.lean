-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_X_2b090bd40426
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_X_2b090bd40426
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:38.158968+00:00
-- url     : https://prove2.me/theorems/079457f9-5ac0-4de1-8e29-e4a46498b6a1
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly X 2b090bd40426: P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly X 2b090bd40426
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly X 2b090bd40426 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly X 2b090bd40426 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L121-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
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
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_X_2b090bd40426 (p : Par e n) : fromPoly Q j e (X p) = toChart Q j e (C (X p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«fromPoly_X» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_X_2b090bd40426
