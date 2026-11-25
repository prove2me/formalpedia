-- Prove2me | Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hilbert_schmidt_mul_le
-- name    : PositivityTheory.CW.HilbertSchmidtNorm.hilbert_schmidt_mul_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:10.327451+00:00
-- url     : https://prove2.me/theorems/dd6f8b57-aa81-4771-b2c5-66095755fc53
-- title:
--   Hilbert Schmidt Norm: hilbert schmidt mul le
-- statement:
--   The Hilbert Schmidt Norm construction uses the hilbert schmidt mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/SecondDerivativeHolds.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/SecondDerivativeHolds.lean#L32-L45

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds
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
open PositivityTheory.CW.HilbertSchmidtNorm
variable {n : ℕ}

theorem PositivityTheory.CW.HilbertSchmidtNorm.hilbert_schmidt_mul_le (g X : Matrix (Fin n) (Fin n) ℂ) : hs2 (g * X) ≤ hs2 g * hs2 X := by sorry
