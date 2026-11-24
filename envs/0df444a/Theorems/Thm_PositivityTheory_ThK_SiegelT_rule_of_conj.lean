-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SiegelT_rule_of_conj
-- name    : PositivityTheory.ThK.SiegelT.rule_of_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:51.134904+00:00
-- url     : https://prove2.me/theorems/13fede22-8c99-4b3c-aeb8-e7f2300b3b46
-- title:
--   Siegel T: rule of conj
-- statement:
--   The Siegel T construction uses the rule of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAlg.lean#L34-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAlg.lean#L34-L84

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']
omit [DecidableEq α]

theorem PositivityTheory.ThK.SiegelT.rule_of_conj [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle} {C1 : Matrix β ν E} {C2 : Matrix β ν' E}
    {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)} (hs : IsSplitting C ψ d (actB c) om) (γ : UG c JB) (s : Matrix ν' ν E)
    (s' : Matrix ν ν' E) (h1 : s * s' = 1) (h2 : s' * s = 1) (hγ : ((γ : GL β E) : Matrix β β E) * C1 = C2 * s)
    (h : SiegelRule c C ψ ξ JA JB d χ C1 om) : SiegelRule c C ψ ξ JA JB d χ C2 om := by sorry
