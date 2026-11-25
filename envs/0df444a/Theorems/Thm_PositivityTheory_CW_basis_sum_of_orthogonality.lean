-- Prove2me | Theorems.Thm_PositivityTheory_CW_basis_sum_of_orthogonality
-- name    : PositivityTheory.CW.basis_sum_of_orthogonality
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:01.601887+00:00
-- url     : https://prove2.me/theorems/2b869d92-0c8e-4b49-8113-cda07fc106fa
-- title:
--   CW: basis sum of orthogonality
-- statement:
--   The CW construction uses the basis sum of orthogonality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/WordFiltrationCommute.lean#L77-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/WordFiltrationCommute.lean#L77-L121

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_WordFiltrationCommute
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
open EigenSumRepresentation

theorem PositivityTheory.CW.basis_sum_of_orthogonality : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt → BasisSumAsFormValues := by sorry
