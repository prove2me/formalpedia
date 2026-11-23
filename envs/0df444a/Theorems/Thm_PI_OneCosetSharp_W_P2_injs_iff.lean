-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_P2_injs_iff
-- name    : PI.OneCosetSharp.W.P2.injs_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:28.932631+00:00
-- url     : https://prove2.me/theorems/9624b17d-67cc-4fac-8d4e-5a9d68dfd84c
-- title:
--   P2: injs iff
-- statement:
--   The P2 construction uses the injs iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean#L145-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean#L145-L164

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.P2
variable {k : Type} [Field k]
variable {k₀ m t b : ℕ}

theorem PI.OneCosetSharp.W.P2.injs_iff {c n : ℕ} (hk : k₀ ≤ n) (hr : k₀ + m - 1 ≤ n + c) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    InJS k₀ m t c n κ ↔ Pm k₀ hk κ ∈ alg (k := k) k₀ m t (n + c) ∧ ∀ p : Fin (n + c), p.1 < k₀ + m - 1 → Pm k₀ hk κ p p = 1 := by sorry
