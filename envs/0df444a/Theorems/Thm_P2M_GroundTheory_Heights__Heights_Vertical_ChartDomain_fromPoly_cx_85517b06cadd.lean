-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_cx_85517b06cadd
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_cx_85517b06cadd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:50.145393+00:00
-- url     : https://prove2.me/theorems/f018dff6-31b6-4d04-b107-69ff5d788d0c
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly cx 85517b06cadd: P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly cx 85517b06cadd
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly cx 85517b06cadd construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly cx 85517b06cadd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L118-L119

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_cx_85517b06cadd (l : Fin n) : fromPoly Q j e (cx Q j e l) = toChart Q j e (X l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«fromPoly_cx» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_cx_85517b06cadd
