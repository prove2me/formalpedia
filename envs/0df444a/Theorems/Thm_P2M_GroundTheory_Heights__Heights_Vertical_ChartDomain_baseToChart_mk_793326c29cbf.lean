-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_baseToChart_mk_793326c29cbf
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_baseToChart_mk_793326c29cbf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:22.738159+00:00
-- url     : https://prove2.me/theorems/e0e5a06b-4711-4511-893b-f407c897591a
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain base To Chart mk 793326c29cbf: P2 M Ground Theory Heights  Heights Vertical Chart Domain base To Chart mk 793326c29cbf
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain base To Chart mk 793326c29cbf construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain base To Chart mk 793326c29cbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L113-L116

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_baseToChart_mk_793326c29cbf (p : MvPolynomial (Fin n) D) :
    baseToChart Q j e (algebraMap _ (Base Q j) (Ideal.Quotient.mk Q p)) =
      toChart Q j e (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D) p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«baseToChart_mk» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_baseToChart_mk_793326c29cbf
