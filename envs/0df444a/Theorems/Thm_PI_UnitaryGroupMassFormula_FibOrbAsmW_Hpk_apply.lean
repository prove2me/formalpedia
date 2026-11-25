-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_Hpk_apply
-- name    : PI.UnitaryGroupMassFormula.FibOrbAsmW.Hpk_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:12.354659+00:00
-- url     : https://prove2.me/theorems/7cfa41b7-22af-4fc9-9b4f-e294917c5254
-- title:
--   Fib Orb Asm W: Hpk apply
-- statement:
--   The Fib Orb Asm W construction uses the Hpk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L18-L23

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

theorem PI.UnitaryGroupMassFormula.FibOrbAsmW.Hpk_apply (k r : ℕ) (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l = sig k r i then sgn k r i else 0 := by sorry
