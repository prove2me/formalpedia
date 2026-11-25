-- Prove2me | Theorems.Thm_SchrodingerSchwartzBruhat_GlobalTheory_CompanionTheory_SchrSB_schr_mem_SB
-- name    : SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:11:11.706699+00:00
-- url     : https://prove2.me/theorems/fcf26231-2c6c-4c87-8e8a-cce15ce4dea2
-- title:
--   Schr SB: schr mem SB
-- statement:
--   The Schr SB construction uses the schr mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchroedingerOperatorHeisenbergPreservesSchwartzB.lean#L55-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchroedingerOperatorHeisenbergPreservesSchwartzB.lean#L55-L69

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsBisSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergPreservesSchwartzB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchrodingerSchwartzBruhat
open MeasureTheory Matrix
open SchrodingerSchwartzBruhat.GlobalTheory SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by sorry
