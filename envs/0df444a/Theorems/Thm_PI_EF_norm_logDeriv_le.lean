-- Prove2me | Theorems.Thm_PI_EF_norm_logDeriv_le
-- name    : PI.EF.norm_logDeriv_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:39.121153+00:00
-- url     : https://prove2.me/theorems/b8b43880-a7ed-40ca-b641-9eb924906ad4
-- title:
--   EF: norm log Deriv le
-- statement:
--   The EF construction uses the norm log Deriv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogDerivBounds.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogDerivBounds.lean#L47-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter

theorem PI.EF.norm_logDeriv_le {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3)
    (h0 : LFunction χ s ≠ 0) (hs0 : 1 / 2 ≤ ‖s‖) (hs1 : 1 / 2 ≤ ‖s - 1‖) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖logDeriv (LFunction χ) s‖ ≤
      Cl * Real.log (N * (|s.im| + 2)) + Cw * Real.log (N * (|s.im| + 2)) / d + 4 := by sorry
