-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_P2_ent_eq
-- name    : PI.OneCosetSharp.W.P2.ent_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:01.297814+00:00
-- url     : https://prove2.me/theorems/b9dc678f-2692-4875-9d7b-4236f8517f25
-- title:
--   P2: ent eq
-- statement:
--   The P2 construction uses the ent eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean#L128-L134

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

theorem PI.OneCosetSharp.W.P2.ent_eq {c n : ℕ} (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (p q : Fin (n + c)) :
    ent k₀ c n c n κ.toLinearMap p.1 q.1 = Pm k₀ hk κ p q := by sorry
