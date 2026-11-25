-- Prove2me | Theorems.Thm_PI_SqPair_LCP_phyp_reindex
-- name    : PI.SqPair.LCP.phyp_reindex
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:46.973505+00:00
-- url     : https://prove2.me/theorems/26a4c1e6-b694-5ea4-9f1a-1dd711848fc0
-- title:
--   LCP: phyp reindex
-- statement:
--   The LCP construction uses the phyp reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L105-L111

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

theorem PI.SqPair.LCP.phyp_reindex {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {ϖ : R} {A A' h : Matrix ι ι R} {k : ℕ} (hP : PHyp ϖ A A' h k) :
    PHyp ϖ (A.submatrix s s) (A'.submatrix s s) (h.submatrix s s) k := by sorry
