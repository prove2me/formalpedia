-- Prove2me | Theorems.Thm_PI_TwNormLat_W_mem_Ufl_iff
-- name    : PI.TwNormLat.W.mem_Ufl_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:29:20.783965+00:00
-- url     : https://prove2.me/theorems/fbab812a-b913-44f7-9cbf-8b6e92448b80
-- title:
--   W: mem Ufl iff
-- statement:
--   The W construction uses the mem Ufl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/CombinationEquivInvMemUnipotentFlagGroup.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/CombinationEquivInvMemUnipotentFlagGroup.lean#L92-L94

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_CombinationEquivInvMemUnipotentFlagGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {K : Type} [Field K] {n : ℕ}

theorem PI.TwNormLat.W.mem_Ufl_iff {N c i : ℕ} (v : Fin (N + c) → K) : v ∈ Loc.Ufl K N c i ↔ Zab (N + i) v := by sorry
