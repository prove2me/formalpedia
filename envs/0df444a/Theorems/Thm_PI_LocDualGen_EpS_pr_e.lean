-- Prove2me | Theorems.Thm_PI_LocDualGen_EpS_pr_e
-- name    : PI.LocDualGen.EpS.pr_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:33.488458+00:00
-- url     : https://prove2.me/theorems/d2866332-2b86-4896-bf99-6b38f3db063f
-- title:
--   Ep S: pr e
-- statement:
--   The Ep S construction uses the pr e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L89-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module
open PI PI.LocDualGen PI.LocDualGen.EpS
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
variable (hr : finrank K L = 2) (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1)

theorem PI.LocDualGen.EpS.pr_e : pr hr e he h0 h1 0 e = 1 ∧ pr hr e he h0 h1 1 e = 0 := by sorry
