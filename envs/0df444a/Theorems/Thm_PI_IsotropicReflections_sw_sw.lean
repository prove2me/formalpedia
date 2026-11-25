-- Prove2me | Theorems.Thm_PI_IsotropicReflections_sw_sw
-- name    : PI.IsotropicReflections.sw_sw
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:14:26.9588+00:00
-- url     : https://prove2.me/theorems/e3c1a6f5-9205-4887-ad8e-5471253c527e
-- title:
--   Isotropic Reflections: sw sw
-- statement:
--   The Isotropic Reflections construction uses the sw sw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L59-L65

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

theorem PI.IsotropicReflections.sw_sw (l : Fin r) (p : Fin (2 * r + k + 1)) : sw l (sw l p) = p := by sorry
