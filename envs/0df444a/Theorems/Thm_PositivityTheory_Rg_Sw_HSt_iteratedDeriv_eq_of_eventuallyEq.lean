-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_iteratedDeriv_eq_of_eventuallyEq
-- name    : PositivityTheory.Rg.Sw.HSt.iteratedDeriv_eq_of_eventuallyEq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:03.761067+00:00
-- url     : https://prove2.me/theorems/413ee6c3-ac98-42dc-a271-143486690c85
-- title:
--   HSt: iterated Deriv eq of eventually Eq
-- statement:
--   The HSt construction uses the iterated Deriv eq of eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/IteratedDerivEqOfEventuallyEq.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/IteratedDerivEqOfEventuallyEq.lean#L9-L12

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

theorem PositivityTheory.Rg.Sw.HSt.iteratedDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) (k : ℕ) :
    iteratedDeriv k f s = iteratedDeriv k g s := by sorry
