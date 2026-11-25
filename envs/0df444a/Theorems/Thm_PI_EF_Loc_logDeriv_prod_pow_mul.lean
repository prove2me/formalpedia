-- Prove2me | Theorems.Thm_PI_EF_Loc_logDeriv_prod_pow_mul
-- name    : PI.EF.Loc.logDeriv_prod_pow_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:27:43.367118+00:00
-- url     : https://prove2.me/theorems/79e1d1ae-60fe-4900-9572-b3fe655ea945
-- title:
--   Loc: log Deriv prod pow mul
-- statement:
--   The Loc construction uses the log Deriv prod pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean#L65-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean#L65-L82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology ComplexConjugate

theorem PI.EF.Loc.logDeriv_prod_pow_mul {Z : Finset ℂ} {m : ℂ → ℕ} {φ : ℂ → ℂ → ℂ} {h : ℂ → ℂ} {s : ℂ}
    (hφ : ∀ ρ ∈ Z, φ ρ s ≠ 0) (hφd : ∀ ρ ∈ Z, DifferentiableAt ℂ (φ ρ) s) (hh : h s ≠ 0)
    (hhd : DifferentiableAt ℂ h s) :
    logDeriv (fun z => (∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) * h z) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (φ ρ) s) + logDeriv h s := by sorry
