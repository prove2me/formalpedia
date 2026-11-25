-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_lagY_iso
-- name    : PositivityTheory.ThK.LinAct.lagY_iso
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:22.945728+00:00
-- url     : https://prove2.me/theorems/b2f205e6-15a9-4d27-b856-50a81ef1bc75
-- title:
--   Lin Act: lag Y iso
-- statement:
--   The Lin Act construction uses the lag Y iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean#L38-L49

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
omit [DecidableEq α] [DecidableEq β] [DecidableEq ν]

theorem PositivityTheory.ThK.LinAct.lagY_iso {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c ξ JB JA) κ) {Cy : Matrix β ν K}
    (h : Cyᵀ * JB * Cy.map c = 0) : ∀ w ∈ lagY d Cy, ∀ w' ∈ lagY d Cy, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2 := by sorry
