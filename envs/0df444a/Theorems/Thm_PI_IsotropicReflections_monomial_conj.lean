-- Prove2me | Theorems.Thm_PI_IsotropicReflections_monomial_conj
-- name    : PI.IsotropicReflections.monomial_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:22:56.388796+00:00
-- url     : https://prove2.me/theorems/2b4d13ce-bc21-5e23-beac-5d613f21e14e
-- title:
--   Isotropic Reflections: monomial conj
-- statement:
--   The Isotropic Reflections construction uses the monomial conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean#L122-L130

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

theorem PI.IsotropicReflections.monomial_conj {m : ℕ} (w H : Matrix (Fin m) (Fin m) ℂ) (σ : Fin m → Fin m) (α : Fin m → ℂ)
    (hw : ∀ i q, w i q = if i = σ q then α q else 0) (p q : Fin m) :
    (wᴴ * H * w) p q = star (α p) * H (σ p) (σ q) * α q := by sorry
