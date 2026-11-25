-- Prove2me | Theorems.Thm_PI_IsotropicReflections_reflection_mem_Glev_castSucc
-- name    : PI.IsotropicReflections.reflection_mem_Glev_castSucc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:10.206106+00:00
-- url     : https://prove2.me/theorems/f4889678-b22c-4b33-9aca-3dac50b658f9
-- title:
--   Isotropic Reflections: reflection mem Glev cast Succ
-- statement:
--   The Isotropic Reflections construction uses the reflection mem Glev cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L158-L165

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

theorem PI.IsotropicReflections.reflection_mem_Glev_castSucc (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ Glev k r l.castSucc := by sorry
