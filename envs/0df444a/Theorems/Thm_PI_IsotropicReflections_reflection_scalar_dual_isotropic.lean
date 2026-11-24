-- Prove2me | Theorems.Thm_PI_IsotropicReflections_reflection_scalar_dual_isotropic
-- name    : PI.IsotropicReflections.reflection_scalar_dual_isotropic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:00:02.763606+00:00
-- url     : https://prove2.me/theorems/dd140997-e4b5-4202-9859-aa2a9f6aa19b
-- title:
--   Isotropic Reflections: reflection scalar dual isotropic
-- statement:
--   The Isotropic Reflections construction uses the reflection scalar dual isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L44-L45

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

theorem PI.IsotropicReflections.reflection_scalar_dual_isotropic (l : Fin r) (c : ℂ) : al (k := k) l c (esI k r l) = (star c)⁻¹ := by sorry
