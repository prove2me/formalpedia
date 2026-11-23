-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_HaarBox_modF_nonneg__f21040a49df2
-- name    : P2M_PI_ProdFormulaE_HaarBox_modF_nonneg__f21040a49df2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:20.411654+00:00
-- url     : https://prove2.me/theorems/d65bd048-0608-4e67-b574-45c9fae86b0f
-- title:
--   P2 M PI Prod Formula E Haar Box mod F nonneg  f21040a49df2: P2 M PI Prod Formula E Haar Box mod F nonneg  f21040a49df2
-- statement:
--   The P2 M PI Prod Formula E Haar Box mod F nonneg  f21040a49df2 construction uses the P2 M PI Prod Formula E Haar Box mod F nonneg  f21040a49df2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarMain.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarMain.lean#L15-L18

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
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem P2M_PI_ProdFormulaE_HaarBox_modF_nonneg__f21040a49df2 (a : K) : 0 ≤ modF K a := by sorry

alias «PI».«ProdFormulaE».«HaarBox».«modF_nonneg'» := P2M_PI_ProdFormulaE_HaarBox_modF_nonneg__f21040a49df2
