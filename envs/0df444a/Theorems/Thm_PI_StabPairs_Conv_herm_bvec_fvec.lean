-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_herm_bvec_fvec
-- name    : PI.StabPairs.Conv.herm_bvec_fvec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:01.232404+00:00
-- url     : https://prove2.me/theorems/f745d048-c202-52dc-b33b-2e2f1997e5d0
-- title:
--   Conv: herm bvec fvec
-- statement:
--   The Conv construction uses the herm bvec fvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L171-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L171-L187

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec
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

theorem PI.StabPairs.Conv.herm_bvec_fvec (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1))
    (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin (r + 1)) (ha : a.val < r) :
    herm (Hpk k r) (bvec j) (fvec k r z a) = 0 := by sorry
