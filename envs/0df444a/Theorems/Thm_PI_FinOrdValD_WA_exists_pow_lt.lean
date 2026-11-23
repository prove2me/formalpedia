-- Prove2me | Theorems.Thm_PI_FinOrdValD_WA_exists_pow_lt
-- name    : PI.FinOrdValD.WA.exists_pow_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:46.717716+00:00
-- url     : https://prove2.me/theorems/28f7402b-a42c-447d-85f7-287ad2a0b979
-- title:
--   WA: exists pow lt
-- statement:
--   The WA construction uses the exists pow lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L18-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]

theorem PI.FinOrdValD.WA.exists_pow_lt {δ : ℤᵐ⁰} (hδ : δ ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < δ := by sorry
