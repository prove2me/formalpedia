-- Prove2me | Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hilbert_schmidt_nonneg_alt
-- name    : PositivityTheory.CW.HilbertSchmidtNorm.hilbert_schmidt_nonneg_alt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:50:33.956919+00:00
-- url     : https://prove2.me/theorems/83acac0d-b51c-5960-b150-6ab253446db6
-- title:
--   Hilbert Schmidt Norm: hilbert schmidt nonneg alt
-- statement:
--   The Hilbert Schmidt Norm construction uses the hilbert schmidt nonneg alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/SecondDerivativeHolds.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/SecondDerivativeHolds.lean#L29-L30

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

theorem PositivityTheory.CW.HilbertSchmidtNorm.hilbert_schmidt_nonneg_alt (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g := by sorry
