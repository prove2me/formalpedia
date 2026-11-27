-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_leib
-- name    : PositivityTheory.Rg.Sw.HSt.leib
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:52:47.552835+00:00
-- url     : https://prove2.me/theorems/489dda42-88d4-49ac-8da5-fb7c2671780c
-- title:
--   HSt: leib
-- statement:
--   The HSt construction uses the leib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/IteratedDerivEqOfEventuallyEq.lean#L14-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/IteratedDerivEqOfEventuallyEq.lean#L14-L42

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_IteratedDerivEqOfEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology Set
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt

theorem PositivityTheory.Rg.Sw.HSt.leib {U : Set ℂ} (hU : IsOpen U) : ∀ (j : ℕ) (h₁ h₂ : ℂ → ℂ), DifferentiableOn ℂ h₁ U → DifferentiableOn ℂ h₂ U →
    ∀ s ∈ U, iteratedDeriv j (fun z => h₁ z * h₂ z) s =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i h₁ s * iteratedDeriv (j - i) h₂ s := by sorry
