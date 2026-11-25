-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_UH_mul
-- name    : PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:33.630154+00:00
-- url     : https://prove2.me/theorems/67314322-d00b-4503-ae41-89365a04ca6a
-- title:
--   Fib Orb Asm W: UH mul
-- statement:
--   The Fib Orb Asm W construction uses the UH mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L61-L67

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_mul {H a b : Matrix ι ι ℂ} (ha : a ∈ UH H) (hb : b ∈ UH H) : a * b ∈ UH H := by sorry
