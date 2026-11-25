-- Prove2me | Theorems.Thm_PI_SqPair_LCP_pconcl_reindex
-- name    : PI.SqPair.LCP.pconcl_reindex
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:46.363271+00:00
-- url     : https://prove2.me/theorems/1aa2160e-9a1f-5a3d-82bf-0de53853a42f
-- title:
--   LCP: pconcl reindex
-- statement:
--   The LCP construction uses the pconcl reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L121-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L121-L132

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
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
variable {R : Type} [CommRing R] [StarRing R]

theorem PI.SqPair.LCP.pconcl_reindex {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {A h : Matrix ι ι R} (hc : PConcl (A.submatrix s s) (h.submatrix s s)) :
    PConcl A h := by sorry
