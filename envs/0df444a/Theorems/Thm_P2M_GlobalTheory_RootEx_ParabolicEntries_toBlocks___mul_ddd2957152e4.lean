-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RootEx_ParabolicEntries_toBlocks___mul_ddd2957152e4
-- name    : P2M_GlobalTheory_RootEx_ParabolicEntries_toBlocks___mul_ddd2957152e4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:49.394021+00:00
-- url     : https://prove2.me/theorems/228faeb3-4a11-4885-bd82-4c0c56d0e130
-- title:
--   P2 M Global Theory Root Ex Parabolic Entries to Blocks   mul ddd2957152e4: P2 M Global Theory Root Ex Parabolic Entries to Blocks   mul ddd2957152e4
-- statement:
--   The P2 M Global Theory Root Ex Parabolic Entries to Blocks   mul ddd2957152e4 construction uses the P2 M Global Theory Root Ex Parabolic Entries to Blocks   mul ddd2957152e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntri.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntri.lean#L77-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ParabolicEntries
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem P2M_GlobalTheory_RootEx_ParabolicEntries_toBlocks___mul_ddd2957152e4 {L : ℕ} {b : Fin c → ℕ} {g h : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b)
    (hh : h ∈ parGroup k n L b) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by sorry

alias «GlobalTheory».«RootEx».«ParabolicEntries».«toBlocks₁₁_mul» := P2M_GlobalTheory_RootEx_ParabolicEntries_toBlocks___mul_ddd2957152e4
