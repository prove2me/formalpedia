-- Prove2me | Theorems.Thm_PI_SqPair_LCP_pgen_main
-- name    : PI.SqPair.LCP.pgen_main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:40.366832+00:00
-- url     : https://prove2.me/theorems/5d94b8e2-adc3-5b5b-bf40-2917620c3989
-- title:
--   LCP: pgen main
-- statement:
--   The LCP construction uses the pgen main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L136-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L136-L168

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

theorem PI.SqPair.LCP.pgen_main (hB : BaseLag) (hS : Step) {R : Type} [CommRing R] [StarRing R]
    (R₀ : Subring R) [HenselianLocalRing R₀] [Finite (IsLocalRing.ResidueField R₀)] (ϖ : R)
    (hI : Inert R₀ ϖ) (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι = n → Even n → PGen ϖ ι := by sorry
