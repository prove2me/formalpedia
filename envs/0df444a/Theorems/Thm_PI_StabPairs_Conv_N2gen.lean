-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_N2gen
-- name    : PI.StabPairs.Conv.N2gen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:33.314689+00:00
-- url     : https://prove2.me/theorems/d0f05e3e-eee0-5940-8284-c8b5416547e6
-- title:
--   Conv: N2gen
-- statement:
--   The Conv construction uses the N2gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L189-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L189-L224

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

theorem PI.StabPairs.Conv.N2gen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r)
    {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) (hM : M * Ff k r z = Ff k r z * u)
    (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    M i (eI k r a) = if i = eI k r a then 1 else 0 := by sorry
