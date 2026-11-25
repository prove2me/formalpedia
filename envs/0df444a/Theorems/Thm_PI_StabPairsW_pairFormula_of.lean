-- Prove2me | Theorems.Thm_PI_StabPairsW_pairFormula_of
-- name    : PI.StabPairsW.pairFormula_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:42.062481+00:00
-- url     : https://prove2.me/theorems/653a789f-9ebf-4756-a058-84539d1c81da
-- title:
--   Stab Pairs W: pair Formula of
-- statement:
--   The Stab Pairs W construction uses the pair Formula of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L218-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L218-L250

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem PI.StabPairsW.pairFormula_of (hG : GramInv) : PairFormula := by sorry
