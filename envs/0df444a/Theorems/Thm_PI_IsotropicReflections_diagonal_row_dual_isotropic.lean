-- Prove2me | Theorems.Thm_PI_IsotropicReflections_diagonal_row_dual_isotropic
-- name    : PI.IsotropicReflections.diagonal_row_dual_isotropic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:10:12.317174+00:00
-- url     : https://prove2.me/theorems/b58857b0-acfd-5db9-b9b4-2eecb02b8e22
-- title:
--   Isotropic Reflections: diagonal row dual isotropic
-- statement:
--   The Isotropic Reflections construction uses the diagonal row dual isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L188-L194

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

theorem PI.IsotropicReflections.diagonal_row_dual_isotropic (j : Fin (2 * r + k + 1)) : g (esI k r l) j = if j = esI k r l then 1 else 0 := by sorry
