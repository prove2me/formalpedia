-- Prove2me | Theorems.Thm_PI_IsotropicReflections_reflection_hermitian_value
-- name    : PI.IsotropicReflections.reflection_hermitian_value
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:31.580781+00:00
-- url     : https://prove2.me/theorems/d3a7fc7f-45e3-5382-a69b-0bdc5088682a
-- title:
--   Isotropic Reflections: reflection hermitian value
-- statement:
--   The Isotropic Reflections construction uses the reflection hermitian value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L224-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L224-L233

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
variable (l : Fin r) (g : Mx k r) (hg : g ∈ Glev k r l.succ)
include hg

theorem PI.IsotropicReflections.reflection_hermitian_value (c : ℂ) :
    herm (Hpk k r) ((w1 k r l c * g) *ᵥ bvec (eI k r l)) (bvec (eI k r l)) = c := by sorry
