-- Prove2me | Theorems.Thm_PI_SqPair_LCP_sel_smul_cancel
-- name    : PI.SqPair.LCP.sel_smul_cancel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:28.648477+00:00
-- url     : https://prove2.me/theorems/f7e9d321-d841-5d0b-b36a-ad01739cfe7d
-- title:
--   LCP: sel smul cancel
-- statement:
--   The LCP construction uses the sel smul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelCore.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelCore.lean#L47-L52

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

theorem PI.SqPair.LCP.sel_smul_cancel {ι κ : Type} {c : R} (hc : c ≠ 0) {X Y : Matrix ι κ R}
    (h : c • X = c • Y) : X = Y := by sorry
