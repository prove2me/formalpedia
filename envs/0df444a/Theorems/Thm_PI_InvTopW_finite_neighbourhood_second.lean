-- Prove2me | Theorems.Thm_PI_InvTopW_finite_neighbourhood_second
-- name    : PI.InvTopW.finite_neighbourhood_second
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:28:19.015178+00:00
-- url     : https://prove2.me/theorems/14a35da6-584b-4612-ba06-62b49cf39d8a
-- title:
--   Inv Top W: finite neighbourhood second
-- statement:
--   The Inv Top W construction uses the finite neighbourhood second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L63-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L63-L127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Topology Filter

theorem PI.InvTopW.finite_neighbourhood_second : FinNhdB := by sorry
