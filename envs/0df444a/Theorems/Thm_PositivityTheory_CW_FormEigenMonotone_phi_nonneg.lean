-- Prove2me | Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_phi_nonneg
-- name    : PositivityTheory.CW.FormEigenMonotone.phi_nonneg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:57.085746+00:00
-- url     : https://prove2.me/theorems/62cd1dfc-27e2-5697-8284-3dc675dce482
-- title:
--   Form Eigen Monotone: phi nonneg
-- statement:
--   The Form Eigen Monotone construction uses the phi nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L11-L11

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FormEigenMonotone

theorem PositivityTheory.CW.FormEigenMonotone.phi_nonneg (s : ℕ) (R x : ℝ) : 0 ≤ phiR s R x := by sorry
