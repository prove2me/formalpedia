-- Prove2me | Theorems.Thm_PI_IsotropicReflections_diagonal_column_dual_isotropic
-- name    : PI.IsotropicReflections.diagonal_column_dual_isotropic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:38:48.728808+00:00
-- url     : https://prove2.me/theorems/cff0fa04-f681-41da-b353-98424480e022
-- title:
--   Isotropic Reflections: diagonal column dual isotropic
-- statement:
--   The Isotropic Reflections construction uses the diagonal column dual isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L180-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L180-L186

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

theorem PI.IsotropicReflections.diagonal_column_dual_isotropic (i : Fin (2 * r + k + 1)) : g i (esI k r l) = if i = esI k r l then 1 else 0 := by sorry
