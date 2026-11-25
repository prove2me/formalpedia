-- Prove2me | Theorems.Thm_PI_InvTopW_natCast_apply
-- name    : PI.InvTopW.natCast_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:37.357103+00:00
-- url     : https://prove2.me/theorems/971c3290-2e0e-4d4b-a402-300b0923350b
-- title:
--   Inv Top W: nat Cast apply
-- statement:
--   The Inv Top W construction uses the nat Cast apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L32-L40

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

theorem PI.InvTopW.natCast_apply (F : Type) [Field F] [NumberField F] (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (N : FiniteAdeleRing (𝓞 F) F) v = (N : v.adicCompletion F) := by sorry
