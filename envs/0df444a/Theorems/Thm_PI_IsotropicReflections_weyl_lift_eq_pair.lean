-- Prove2me | Theorems.Thm_PI_IsotropicReflections_weyl_lift_eq_pair
-- name    : PI.IsotropicReflections.weyl_lift_eq_pair
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:00.018918+00:00
-- url     : https://prove2.me/theorems/226994c0-6534-493f-bdd3-4b841bd5a531
-- title:
--   Isotropic Reflections: weyl lift eq pair
-- statement:
--   The Isotropic Reflections construction uses the weyl lift eq pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L67-L72

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

theorem PI.IsotropicReflections.weyl_lift_eq_pair (l : Fin r) (c : ℂ) (i q : Fin (2 * r + k + 1)) :
    w1 k r l c i q = if i = sw l q then al l c q else 0 := by sorry
