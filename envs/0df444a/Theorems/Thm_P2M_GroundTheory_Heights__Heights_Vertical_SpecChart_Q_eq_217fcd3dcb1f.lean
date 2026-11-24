-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_eq_217fcd3dcb1f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_eq_217fcd3dcb1f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:47.86836+00:00
-- url     : https://prove2.me/theorems/08b8c47f-5464-4ba5-ba16-ef81397c2bca
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart Q eq 217fcd3dcb1f: P2 M Ground Theory Heights  Heights Vertical Spec Chart Q eq 217fcd3dcb1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart Q eq 217fcd3dcb1f construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart Q eq 217fcd3dcb1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L88-L89

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
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_eq_217fcd3dcb1f : Q e I j W = (Wb I j W).map C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«Q_eq» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_eq_217fcd3dcb1f
