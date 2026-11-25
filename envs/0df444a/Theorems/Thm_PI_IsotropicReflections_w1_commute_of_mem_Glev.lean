-- Prove2me | Theorems.Thm_PI_IsotropicReflections_w1_commute_of_mem_Glev
-- name    : PI.IsotropicReflections.w1_commute_of_mem_Glev
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:37.058791+00:00
-- url     : https://prove2.me/theorems/70ff93d4-6a31-50c5-95c7-caea2772042d
-- title:
--   Isotropic Reflections: w1 commute of mem Glev
-- statement:
--   The Isotropic Reflections construction uses the w1 commute of mem Glev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L211-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L211-L222

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

theorem PI.IsotropicReflections.w1_commute_of_mem_Glev (c : ℂ) : w1 k r l c * g = g * w1 k r l c := by sorry
