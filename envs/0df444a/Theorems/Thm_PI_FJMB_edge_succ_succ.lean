-- Prove2me | Theorems.Thm_PI_FJMB_edge_succ_succ
-- name    : PI.FJMB.edge_succ_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:33.217519+00:00
-- url     : https://prove2.me/theorems/3cf3cb79-d74a-4d85-9d4c-7c3b40ab89a0
-- title:
--   FJMB: edge succ succ
-- statement:
--   The FJMB construction uses the edge succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L63-L66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
variable {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
include hι

theorem PI.FJMB.edge_succ_succ (i : Fin m) (k : Fin n) : ι (i.succ, k.succ) ∉ edge ι := by sorry
