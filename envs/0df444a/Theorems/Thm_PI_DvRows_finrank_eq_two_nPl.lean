-- Prove2me | Theorems.Thm_PI_DvRows_finrank_eq_two_nPl
-- name    : PI.DvRows.finrank_eq_two_nPl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:07.459147+00:00
-- url     : https://prove2.me/theorems/7891d144-a1d3-4510-9a9a-711e30cfdec6
-- title:
--   Dv Rows: finrank eq two n Pl
-- statement:
--   The Dv Rows construction uses the finrank eq two n Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean#L38-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
variable {K : Type} [Field K] [NumberField K]

theorem PI.DvRows.finrank_eq_two_nPl [NumberField.IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by sorry
