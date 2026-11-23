-- Prove2me | Theorems.Thm_PI_LocDualGen_EpS_pr_f
-- name    : PI.LocDualGen.EpS.pr_f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:28.680479+00:00
-- url     : https://prove2.me/theorems/8c1b9aae-aca5-43a6-9589-19afd87436ed
-- title:
--   Ep S: pr f
-- statement:
--   The Ep S construction uses the pr f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L95-L97

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

theorem PI.LocDualGen.EpS.pr_f : pr hr e he h0 h1 0 (1 - e) = 0 ∧ pr hr e he h0 h1 1 (1 - e) = 1 := by sorry
