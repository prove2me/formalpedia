-- Prove2me | Theorems.Thm_PI_InvTopW_finite_neighbourhood_first
-- name    : PI.InvTopW.finite_neighbourhood_first
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:45.198003+00:00
-- url     : https://prove2.me/theorems/f0c0b828-5820-57a5-9af6-498520420ef3
-- title:
--   Inv Top W: finite neighbourhood first
-- statement:
--   The Inv Top W construction uses the finite neighbourhood first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L14-L30

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

theorem PI.InvTopW.finite_neighbourhood_first : FinNhdA := by sorry
