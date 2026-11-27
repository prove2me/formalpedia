-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_lowSupp
-- name    : PI.StabPairs.Conv.lowSupp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:12.189137+00:00
-- url     : https://prove2.me/theorems/bc556ea2-f109-57da-8e26-c84c912cd6c3
-- title:
--   Conv: low Supp
-- statement:
--   The Conv construction uses the low Supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L79-L89

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem PI.StabPairs.Conv.lowSupp (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : ℕ) (ha : a ≤ r) (x : Fin (r + 1) → ℂ)
    (hx : ∀ c : Fin (r + 1), a ≤ c.val → x c = 0) (i : Fin (2 * r + k + 1)) (hi : a ≤ i.val) :
    (∑ c, x c • fvec k r z c) i = 0 := by sorry
