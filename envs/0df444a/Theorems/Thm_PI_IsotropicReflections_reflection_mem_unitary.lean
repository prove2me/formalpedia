-- Prove2me | Theorems.Thm_PI_IsotropicReflections_reflection_mem_unitary
-- name    : PI.IsotropicReflections.reflection_mem_unitary
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:28.264727+00:00
-- url     : https://prove2.me/theorems/56d2ec2e-7321-483e-a376-70c96b18e3f7
-- title:
--   Isotropic Reflections: reflection mem unitary
-- statement:
--   The Isotropic Reflections construction uses the reflection mem unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L142-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L142-L149

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}

theorem PI.IsotropicReflections.reflection_mem_unitary (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ UH (Hpk k r) := by sorry
