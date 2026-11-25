-- Prove2me | Theorems.Thm_PI_InvTopW_isOpen_intAd
-- name    : PI.InvTopW.isOpen_intAd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:28.770276+00:00
-- url     : https://prove2.me/theorems/45af99be-ecdc-41d9-905c-150ca852a895
-- title:
--   Inv Top W: is Open int Ad
-- statement:
--   The Inv Top W construction uses the is Open int Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/FiniteNeighbourhoodSecond.lean#L10-L12

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

theorem PI.InvTopW.isOpen_intAd (F : Type) [Field F] [NumberField F] :
    IsOpen ((Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))) := by sorry
