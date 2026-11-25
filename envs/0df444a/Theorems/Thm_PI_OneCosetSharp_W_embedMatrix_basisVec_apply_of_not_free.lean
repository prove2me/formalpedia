-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_embedMatrix_basisVec_apply_of_not_free
-- name    : PI.OneCosetSharp.W.embedMatrix_basisVec_apply_of_not_free
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:18:29.600813+00:00
-- url     : https://prove2.me/theorems/d09ce1e9-11f6-5244-9f14-517cb200d56c
-- title:
--   W: embed Matrix basis Vec apply of not free
-- statement:
--   The W construction uses the embed Matrix basis Vec apply of not free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EmbedMatrixBasisVecApplyOfNotFree.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EmbedMatrixBasisVecApplyOfNotFree.lean#L11-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_GaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EmbedMatrixBasisVecApplyOfNotFree
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
variable {k : Type} [Field k] {n' c n : ℕ}

theorem PI.OneCosetSharp.W.embedMatrix_basisVec_apply_of_not_free (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (tt : FC n' (c + 1) n c → k) (i : ℕ) (hi : i < c)
    (l : Fin (n + c)) (hf : ¬ IsFree n' n c l.1 (n' + i)) :
    xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) l = if l.1 = n + i then 1 else 0 := by sorry
