-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarAlgP_haarAlg_of
-- name    : PI.ProdFormulaE.HaarAlgP.haarAlg_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:48.975027+00:00
-- url     : https://prove2.me/theorems/a3970bf6-76f6-5608-826e-299e07cf3587
-- title:
--   Haar Alg P: haar Alg of
-- statement:
--   The Haar Alg P construction uses the haar Alg of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarMain.lean#L138-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarMain.lean#L138-L159

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarAlgP
open HaarBox

theorem PI.ProdFormulaE.HaarAlgP.haarAlg_of
    (hscale : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] [MeasurableSpace E] [BorelSpace E] (n : ℕ) (b : Basis (Fin n) K E)
      (μ : Measure E) [μ.IsAddHaarMeasure], ScaleBox b μ)
    (htrans : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] (n : ℕ) (b : Basis (Fin n) K E), TransvBox b) :
    St.HaarAlg := by sorry
