-- Prove2me | Theorems.Thm_PI_IsotropicReflections_g_mem_cast
-- name    : PI.IsotropicReflections.g_mem_cast
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:39.149169+00:00
-- url     : https://prove2.me/theorems/3140a80d-e9d8-470f-b8c2-90254ef0713e
-- title:
--   Isotropic Reflections: g mem cast
-- statement:
--   The Isotropic Reflections construction uses the g mem cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L204-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L204-L209

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

theorem PI.IsotropicReflections.g_mem_cast : g ∈ Glev k r l.castSucc := by sorry
