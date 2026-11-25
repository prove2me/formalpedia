-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_mul_intMat_mul
-- name    : PI.UnitaryGroupMassFormula.GelfCpt.mul_intMat_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:30.203801+00:00
-- url     : https://prove2.me/theorems/3f5bdf6d-bf17-5d4c-b361-088858d14172
-- title:
--   Gelf Cpt: mul int Mat mul
-- statement:
--   The Gelf Cpt construction uses the mul int Mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean#L45-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean#L45-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.UnitaryGroupMassFormula.GelfCpt.mul_intMat_mul (μ : Measure G) [IsFiniteMeasure μ] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (M M' : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) :
    (M * intMat μ ρ f * M') i j =
      ∫ g, f g * (M * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * M') i j ∂μ := by sorry
