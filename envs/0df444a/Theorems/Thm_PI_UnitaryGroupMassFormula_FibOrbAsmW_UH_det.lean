-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_UH_det
-- name    : PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_det
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:33:30.764488+00:00
-- url     : https://prove2.me/theorems/67c89fe1-b0c4-4e35-8b6c-b33915d89025
-- title:
--   Fib Orb Asm W: UH det
-- statement:
--   The Fib Orb Asm W construction uses the UH det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L69-L76

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

theorem PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_det {H g : Matrix ι ι ℂ} (hH : IsUnit H.det) (hg : g ∈ UH H) : IsUnit g.det := by sorry
