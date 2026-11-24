-- Prove2me | Theorems.Thm_PI_IsotropicReflections_trich
-- name    : PI.IsotropicReflections.trich
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:57.767516+00:00
-- url     : https://prove2.me/theorems/49d9778c-aea4-43b4-b8b3-c58281dd5b00
-- title:
--   Isotropic Reflections: trich
-- statement:
--   The Isotropic Reflections construction uses the trich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L51-L57

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

theorem PI.IsotropicReflections.trich (l : Fin r) (p : Fin (2 * r + k + 1)) :
    p = eI k r l ∨ p = esI k r l ∨ (p ≠ eI k r l ∧ p ≠ esI k r l) := by sorry
