-- Prove2me | Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_phi_eq
-- name    : PositivityTheory.CW.FormEigenMonotone.phi_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:40.993914+00:00
-- url     : https://prove2.me/theorems/497d5b9c-2a4a-44be-932d-168893dfafa7
-- title:
--   Form Eigen Monotone: phi eq
-- statement:
--   The Form Eigen Monotone construction uses the phi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L29-L36

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

theorem PositivityTheory.CW.FormEigenMonotone.phi_eq {s : ℕ} {R x : ℝ} (hx : 0 ≤ x) (hxR : x < R) :
    phiR s R x = ((1+x)^s)⁻¹ - ((1+R)^s)⁻¹ := by sorry
