-- Prove2me | Theorems.Thm_SchrodingerSchwartzBruhat_GlobalTheory_CompanionTheory_SchrSB_isLocallyConstant_addChar
-- name    : SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.isLocallyConstant_addChar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:59.825682+00:00
-- url     : https://prove2.me/theorems/aff7ec59-1de7-4ab6-9c0e-ddba4f57a5f5
-- title:
--   Schr SB: is Locally Constant add Char
-- statement:
--   The Schr SB construction uses the is Locally Constant add Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchroedingerOperatorHeisenbergPreservesSchwartzB.lean#L23-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchroedingerOperatorHeisenbergPreservesSchwartzB.lean#L23-L53

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

theorem SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.isLocallyConstant_addChar (ψ : AddChar k ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by sorry
