-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_embedMatrix_basisVec_apply_of_le
-- name    : PI.OneCosetSharp.W.embedMatrix_basisVec_apply_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:18:36.474981+00:00
-- url     : https://prove2.me/theorems/fa0929d8-7208-4e21-ae59-57044289cac1
-- title:
--   W: embed Matrix basis Vec apply of le
-- statement:
--   The W construction uses the embed Matrix basis Vec apply of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/Assemble.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/Assemble.lean#L28-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE

theorem PI.OneCosetSharp.W.embedMatrix_basisVec_apply_of_le {k : Type} [Field k] {n' c n : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (tt : FC n' (c + 1) n c → k) (s : ℕ) (hs : s < n') (l : Fin (n + c)) (hl : n ≤ l.1) :
    xx1 xj tt (eN k (n' + (c + 1)) s) l = 0 := by sorry
