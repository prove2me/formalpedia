-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_sgn_sig
-- name    : PI.UnitaryGroupMassFormula.FibOrbAsmW.sgn_sig
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:52.292558+00:00
-- url     : https://prove2.me/theorems/999d577f-eb98-5715-a6d4-5a7f6194b005
-- title:
--   Fib Orb Asm W: sgn sig
-- statement:
--   The Fib Orb Asm W construction uses the sgn sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L30-L33

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FibOrbAsmW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

theorem PI.UnitaryGroupMassFormula.FibOrbAsmW.sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by sorry
