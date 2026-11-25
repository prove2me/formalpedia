-- Prove2me | Theorems.Thm_PI_IsotropicReflections_herm_bvec
-- name    : PI.IsotropicReflections.herm_bvec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:48.882603+00:00
-- url     : https://prove2.me/theorems/5658bd2f-64f4-4514-87c4-5a525825e13e
-- title:
--   Isotropic Reflections: herm bvec
-- statement:
--   The Isotropic Reflections construction uses the herm bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L117-L120

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

theorem PI.IsotropicReflections.herm_bvec {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (j : Fin m) :
    herm H v (bvec j) = (H *ᵥ v) j := by sorry
