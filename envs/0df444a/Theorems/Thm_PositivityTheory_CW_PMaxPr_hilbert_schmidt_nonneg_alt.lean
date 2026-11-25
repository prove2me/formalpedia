-- Prove2me | Theorems.Thm_PositivityTheory_CW_PMaxPr_hilbert_schmidt_nonneg_alt
-- name    : PositivityTheory.CW.PMaxPr.hilbert_schmidt_nonneg_alt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:46.346628+00:00
-- url     : https://prove2.me/theorems/50242d43-87e3-5169-b91c-1dbfe3baabdb
-- title:
--   PMax Pr: hilbert schmidt nonneg alt
-- statement:
--   The PMax Pr construction uses the hilbert schmidt nonneg alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/PMaxPr.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/PMaxPr.lean#L11-L12

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_PMaxPr
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
open PositivityTheory.CW.PMaxPr

theorem PositivityTheory.CW.PMaxPr.hilbert_schmidt_nonneg_alt {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g := by sorry
