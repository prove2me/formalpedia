-- Prove2me | Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_den
-- name    : PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_den
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:24.522824+00:00
-- url     : https://prove2.me/theorems/8bf64069-4cfc-56ae-9b10-3cd43d061f62
-- title:
--   Integers Dense Finite Adeles: exists den
-- statement:
--   The Integers Dense Finite Adeles construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentApproximation/AddDense.lean#L62-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentApproximation/AddDense.lean#L62-L84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnipApproxD PI.UnipApproxD.IntegersDenseFiniteAdeles
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_den (b : FiniteAdeleRing R K) :
    ∃ r : R, r ≠ 0 ∧ IsInt (algebraMap R (FiniteAdeleRing R K) r * b) := by sorry
