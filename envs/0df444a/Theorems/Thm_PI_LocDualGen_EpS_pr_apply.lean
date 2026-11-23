-- Prove2me | Theorems.Thm_PI_LocDualGen_EpS_pr_apply
-- name    : PI.LocDualGen.EpS.pr_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:31.237371+00:00
-- url     : https://prove2.me/theorems/c25176f1-35b6-4106-b9e1-e2fecabdc5b2
-- title:
--   Ep S: pr apply
-- statement:
--   The Ep S construction uses the pr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L87-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L87-L87

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

theorem PI.LocDualGen.EpS.pr_apply (i : Fin 2) (z : L) : pr hr e he h0 h1 i z = (bas hr e he h0 h1).repr z i := by sorry
