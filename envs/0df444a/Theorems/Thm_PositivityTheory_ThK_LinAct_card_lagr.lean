-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_card_lagr
-- name    : PositivityTheory.ThK.LinAct.card_lagr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:24.885132+00:00
-- url     : https://prove2.me/theorems/881863bb-1f75-42af-b861-b365acd97cd3
-- title:
--   Lin Act: card lagr
-- statement:
--   The Lin Act construction uses the card lagr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean#L52-L59

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
set_option linter.unusedSectionVars false
variable {k : Type} [Field k] [Invertible (2 : k)] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
omit [Invertible (2 : k)]

theorem PositivityTheory.ThK.LinAct.card_lagr [Nontrivial K] {JB : Matrix β β K} {Cy : Matrix β ν K} (h : IsLagr c JB Cy) :
    Fintype.card β = 2 * Fintype.card ν := by sorry
