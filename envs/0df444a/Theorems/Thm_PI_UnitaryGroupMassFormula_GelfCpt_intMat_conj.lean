-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_intMat_conj
-- name    : PI.UnitaryGroupMassFormula.GelfCpt.intMat_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:35.106403+00:00
-- url     : https://prove2.me/theorems/2ded9fff-1b1f-4acf-bd8e-667bb748c83a
-- title:
--   Gelf Cpt: int Mat conj
-- statement:
--   The Gelf Cpt construction uses the int Mat conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean#L67-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean#L67-L86

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

theorem PI.UnitaryGroupMassFormula.GelfCpt.intMat_conj (μ : Measure G) [μ.IsHaarMeasure] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (h : G)
    (hA : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f =
      intMat μ ρ f * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) (i j : Fin N) :
    ∫ g, f (h⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ =
      intMat μ ρ f i j := by sorry
