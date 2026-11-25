-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_sgn_mul_self
-- name    : PI.UnitaryGroupMassFormula.FibOrbAsmW.sgn_mul_self
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:11.045423+00:00
-- url     : https://prove2.me/theorems/3d8f0cd0-8670-54c3-909e-95c4699510da
-- title:
--   Fib Orb Asm W: sgn mul self
-- statement:
--   The Fib Orb Asm W construction uses the sgn mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L35-L36

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

theorem PI.UnitaryGroupMassFormula.FibOrbAsmW.sgn_mul_self (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by sorry
