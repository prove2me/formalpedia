-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_EisRk1Cont____eq_tails_8e43976e975c
-- name    : P2M_GlobalTheory_CompanionTheory_EisRk1Cont____eq_tails_8e43976e975c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:42.273988+00:00
-- url     : https://prove2.me/theorems/05c92cab-e5e3-472f-9beb-d5743327dce1
-- title:
--   P2 M Global Theory Companion Theory Eis Rk1 Cont    eq tails 8e43976e975c: P2 M Global Theory Companion Theory Eis Rk1 Cont    eq tails 8e43976e975c
-- statement:
--   The P2 M Global Theory Companion Theory Eis Rk1 Cont    eq tails 8e43976e975c construction uses the P2 M Global Theory Companion Theory Eis Rk1 Cont    eq tails 8e43976e975c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSetIntegralIoiOne.lean#L121-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSetIntegralIoiOne.lean#L121-L200

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSetIntegralIoiOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisRk1Cont

theorem P2M_GlobalTheory_CompanionTheory_EisRk1Cont____eq_tails_8e43976e975c (P : WeakFEPair ℂ) (s : ℂ) :
    P.Λ₀ s = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)) +
      P.ε * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀) := by sorry

alias «GlobalTheory».«CompanionTheory».«EisRk1Cont».«Λ₀_eq_tails» := P2M_GlobalTheory_CompanionTheory_EisRk1Cont____eq_tails_8e43976e975c
