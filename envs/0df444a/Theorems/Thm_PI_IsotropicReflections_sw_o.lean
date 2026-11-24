-- Prove2me | Theorems.Thm_PI_IsotropicReflections_sw_o
-- name    : PI.IsotropicReflections.sw_o
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:07.623081+00:00
-- url     : https://prove2.me/theorems/5f20b108-9c56-4926-bac9-d0b2857c9ed8
-- title:
--   Isotropic Reflections: sw o
-- statement:
--   The Isotropic Reflections construction uses the sw o property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L37-L39

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

theorem PI.IsotropicReflections.sw_o (l : Fin r) {p : Fin (2 * r + k + 1)} (h1 : p ≠ eI k r l) (h2 : p ≠ esI k r l) :
    sw l p = p := by sorry
