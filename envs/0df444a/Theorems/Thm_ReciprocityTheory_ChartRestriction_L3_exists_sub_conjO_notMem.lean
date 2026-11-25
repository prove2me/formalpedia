-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_exists_sub_conjO_notMem
-- name    : ReciprocityTheory.ChartRestriction.L3.exists_sub_conjO_notMem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:32.043699+00:00
-- url     : https://prove2.me/theorems/10b1ff62-b2ca-4bdf-b004-6fdf8c8d2bd6
-- title:
--   L3: exists sub conj O not Mem
-- statement:
--   The L3 construction uses the exists sub conj O not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsSqAbsNormOfInert.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsSqAbsNormOfInert.lean#L39-L49

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem ReciprocityTheory.ChartRestriction.L3.exists_sub_conjO_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ θ : 𝓞 K, θ - conjO K θ ∉ P := by sorry
