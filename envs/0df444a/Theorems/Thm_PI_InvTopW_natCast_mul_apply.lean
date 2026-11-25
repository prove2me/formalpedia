-- Prove2me | Theorems.Thm_PI_InvTopW_natCast_mul_apply
-- name    : PI.InvTopW.natCast_mul_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:42.129793+00:00
-- url     : https://prove2.me/theorems/dd606221-4dba-5976-a0a7-e1ae44cddc94
-- title:
--   Inv Top W: nat Cast mul apply
-- statement:
--   The Inv Top W construction uses the nat Cast mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L42-L46

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

theorem PI.InvTopW.natCast_mul_apply (F : Type) [Field F] [NumberField F] (N : ℕ)
    (z : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : FiniteAdeleRing (𝓞 F) F) * z) v = (N : v.adicCompletion F) * z v := by sorry
