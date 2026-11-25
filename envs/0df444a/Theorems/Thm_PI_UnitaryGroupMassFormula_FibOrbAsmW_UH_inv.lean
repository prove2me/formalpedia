-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_UH_inv
-- name    : PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:43.740817+00:00
-- url     : https://prove2.me/theorems/f3e482dd-8c16-4e9d-916f-403a12810272
-- title:
--   Fib Orb Asm W: UH inv
-- statement:
--   The Fib Orb Asm W construction uses the UH inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean#L78-L87

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

theorem PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_inv {H g : Matrix ι ι ℂ} (hH : IsUnit H.det) (hg : g ∈ UH H) : g⁻¹ ∈ UH H := by sorry
