-- Prove2me | Theorems.Thm_PI_StabPairsW_Sset_frame
-- name    : PI.StabPairsW.Sset_frame
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:51:59.974881+00:00
-- url     : https://prove2.me/theorems/26b3995f-d14a-490c-ad6a-0d24fbbe9869
-- title:
--   Stab Pairs W: Sset frame
-- statement:
--   The Stab Pairs W construction uses the Sset frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L92-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L92-L147

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

theorem PI.StabPairsW.Sset_frame (z : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z) (s : B.Mat k r) (hs : s ∈ Sset k r z) :
    s ∈ B.GV k r ∧ s * Ff k r z = Ff k r z * uMap k r z s ∧ uMap k r z s ∈ UTset (r + 1) := by sorry
