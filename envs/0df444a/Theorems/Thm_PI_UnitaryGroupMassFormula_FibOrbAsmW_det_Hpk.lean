-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_det_Hpk
-- name    : PI.UnitaryGroupMassFormula.FibOrbAsmW.det_Hpk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:58.631314+00:00
-- url     : https://prove2.me/theorems/6d654809-4101-594c-8609-d30905b4aef9
-- title:
--   Fib Orb Asm W: det Hpk
-- statement:
--   The Fib Orb Asm W construction uses the det Hpk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L49-L55

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

theorem PI.UnitaryGroupMassFormula.FibOrbAsmW.det_Hpk (k r : ℕ) : IsUnit (Hpk k r).det := by sorry
