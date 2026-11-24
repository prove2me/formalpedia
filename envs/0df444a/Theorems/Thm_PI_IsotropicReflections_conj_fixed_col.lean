-- Prove2me | Theorems.Thm_PI_IsotropicReflections_conj_fixed_col
-- name    : PI.IsotropicReflections.conj_fixed_col
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:10.737445+00:00
-- url     : https://prove2.me/theorems/915d2995-4ace-4132-ab78-32a0663e199a
-- title:
--   Isotropic Reflections: conj fixed col
-- statement:
--   The Isotropic Reflections construction uses the conj fixed col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L132-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L132-L140

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

theorem PI.IsotropicReflections.conj_fixed_col {m : ℕ} (g H : Matrix (Fin m) (Fin m) ℂ) (p : Fin m)
    (hg : ∀ i, g i p = if i = p then 1 else 0) (q : Fin m) :
    (gᴴ * H * g) p q = ∑ j, H p j * g j q := by sorry
