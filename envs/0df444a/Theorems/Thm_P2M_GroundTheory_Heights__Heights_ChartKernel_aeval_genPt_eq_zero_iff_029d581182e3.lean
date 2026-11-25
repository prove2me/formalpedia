-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genPt_eq_zero_iff_029d581182e3
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genPt_eq_zero_iff_029d581182e3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:23.713047+00:00
-- url     : https://prove2.me/theorems/23d4c00c-2ba4-4fd8-8a92-5f8e7e266ba0
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel aeval gen Pt eq zero iff 029d581182e3: P2 M Ground Theory Heights  Heights Chart Kernel aeval gen Pt eq zero iff 029d581182e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel aeval gen Pt eq zero iff 029d581182e3 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel aeval gen Pt eq zero iff 029d581182e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L103-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L103-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genPt_eq_zero_iff_029d581182e3 (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (g : MvPolynomial (Fin n) F) :
    aeval (genPt I) g = 0 ↔ g ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«aeval_genPt_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genPt_eq_zero_iff_029d581182e3
