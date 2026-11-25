-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_ker_aeval_chart_24e855cde06c
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_ker_aeval_chart_24e855cde06c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:05.616569+00:00
-- url     : https://prove2.me/theorems/b310187c-87ed-5b5a-a775-7d67a52d8701
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel ker aeval chart 24e855cde06c: P2 M Ground Theory Heights  Heights Chart Kernel ker aeval chart 24e855cde06c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel ker aeval chart 24e855cde06c construction uses the P2 M Ground Theory Heights  Heights Chart Kernel ker aeval chart 24e855cde06c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L46-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L46-L101

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_ker_aeval_chart_24e855cde06c (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : IsHomogIdeal I)
    (t : Fin n → F) (hτ : aeval (genPt I) (linForm t) ≠ 0) :
    RingHom.ker (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I)).toRingHom =
      I ⊔ Ideal.span {linForm t - 1} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«ker_aeval_chart» := P2M_GroundTheory_Heights__Heights_ChartKernel_ker_aeval_chart_24e855cde06c
