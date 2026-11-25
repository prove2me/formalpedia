-- Prove2me | Theorems.Thm_PI_IsotropicReflections_reflection_fixes_basis_vector
-- name    : PI.IsotropicReflections.reflection_fixes_basis_vector
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:55:36.87487+00:00
-- url     : https://prove2.me/theorems/3bf83098-932d-4e4d-a10f-c9e93fdd7cd7
-- title:
--   Isotropic Reflections: reflection fixes basis vector
-- statement:
--   The Isotropic Reflections construction uses the reflection fixes basis vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L151-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L151-L156

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

theorem PI.IsotropicReflections.reflection_fixes_basis_vector (l : Fin r) (c : ℂ) (j : Fin (2 * r + k + 1)) (h1 : j ≠ eI k r l) (h2 : j ≠ esI k r l) :
    w1 k r l c *ᵥ bvec j = bvec j := by sorry
