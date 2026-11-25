-- Prove2me | Theorems.Thm_PI_SqPair_LCP_inert_isLocalRing
-- name    : PI.SqPair.LCP.inert_isLocalRing
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:16.312988+00:00
-- url     : https://prove2.me/theorems/abd6a661-3a01-42ca-b9a3-cff65fe688f9
-- title:
--   LCP: inert is Local Ring
-- statement:
--   The LCP construction uses the inert is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L194-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L194-L210

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
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
open PI.SqPair.LocCartanPairW

theorem PI.SqPair.LCP.inert_isLocalRing {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R} {ϖ : R}
    (hI : Inert R₀ ϖ) : IsLocalRing R := by sorry
