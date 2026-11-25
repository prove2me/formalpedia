-- Prove2me | Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_denseRange
-- name    : PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:30.31654+00:00
-- url     : https://prove2.me/theorems/34f43b3e-682d-4bdb-b343-7e6996b52cd6
-- title:
--   Integers Dense Finite Adeles: dense Range
-- statement:
--   The Integers Dense Finite Adeles construction uses the dense Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentApproximation/AddDense.lean#L217-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentApproximation/AddDense.lean#L217-L275

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

theorem PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by sorry
