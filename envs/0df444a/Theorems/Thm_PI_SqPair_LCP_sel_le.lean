-- Prove2me | Theorems.Thm_PI_SqPair_LCP_sel_le
-- name    : PI.SqPair.LCP.sel_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:04.599127+00:00
-- url     : https://prove2.me/theorems/e26a73dd-bb6f-4a23-92a0-df66058fd12f
-- title:
--   LCP: sel le
-- statement:
--   The LCP construction uses the sel le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelCore.lean#L54-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelCore.lean#L54-L82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]

theorem PI.SqPair.LCP.sel_le (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) (m k : ℕ)
    (hrel : ((ϖ ^ m • h₁).map σ)ᵀ * A * (ϖ ^ m • h₁) = ϖ ^ (2 * k) • A') :
    m ≤ k ∧ (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' := by sorry
