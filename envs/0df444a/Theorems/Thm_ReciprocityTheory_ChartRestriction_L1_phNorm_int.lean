-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_phNorm_int
-- name    : ReciprocityTheory.ChartRestriction.L1.phNorm_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:41.883712+00:00
-- url     : https://prove2.me/theorems/86a919a7-0ebe-4e46-833d-2defc1745af8
-- title:
--   L1: ph Norm int
-- statement:
--   The L1 construction uses the ph Norm int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgPhInt.lean#L12-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgPhInt.lean#L12-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveJetsUnitBall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgPhInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem ReciprocityTheory.ChartRestriction.L1.phNorm_int {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hF : C.Frame R l linv ph) (h1 : C.F1 R l linv ph) (hneg : C.PhNormAt R l linv ph (-1) (-1))
    (h2 : (2 : K)⁻¹ ∈ R) (n : ℤ) : C.PhNormAt R l linv ph (n : K) (n : K) := by sorry
