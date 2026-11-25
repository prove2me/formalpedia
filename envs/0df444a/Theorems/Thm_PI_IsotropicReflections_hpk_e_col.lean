-- Prove2me | Theorems.Thm_PI_IsotropicReflections_hpk_e_col
-- name    : PI.IsotropicReflections.hpk_e_col
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:52.505964+00:00
-- url     : https://prove2.me/theorems/981ab5d0-b1f5-507a-8665-e30983c42228
-- title:
--   Isotropic Reflections: hpk e col
-- statement:
--   The Isotropic Reflections construction uses the hpk e col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L98-L103

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

theorem PI.IsotropicReflections.hpk_e_col (l : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (eI k r l) = if i = esI k r l then 1 else 0 := by sorry
