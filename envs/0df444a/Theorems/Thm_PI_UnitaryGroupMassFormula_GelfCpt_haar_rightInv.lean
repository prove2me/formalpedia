-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_haar_rightInv
-- name    : PI.UnitaryGroupMassFormula.GelfCpt.haar_rightInv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:22.261471+00:00
-- url     : https://prove2.me/theorems/23938f52-b52d-45bf-b433-78bb0df87597
-- title:
--   Gelf Cpt: haar right Inv
-- statement:
--   The Gelf Cpt construction uses the haar right Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean#L21-L36

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

theorem PI.UnitaryGroupMassFormula.GelfCpt.haar_rightInv (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by sorry
