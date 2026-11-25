-- Prove2me | Theorems.Thm_PI_WickFormula_comm_pow
-- name    : PI.WickFormula.comm_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:49.073897+00:00
-- url     : https://prove2.me/theorems/59231707-11cf-43b8-bde8-d594951102dc
-- title:
--   Wick Formula: comm pow
-- statement:
--   The Wick Formula construction uses the comm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L68-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA]

theorem PI.WickFormula.comm_pow (b c : AA) (t : k) (h : b * c = c * b + algebraMap k AA t) (n : ℕ) :
    b * c ^ n = c ^ n * b + ((n : k) * t) • c ^ (n - 1) := by sorry
