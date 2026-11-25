-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_adj_closed
-- name    : PositivityTheory.Rg.Sw.LC.CoreA.adj_closed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:34.955185+00:00
-- url     : https://prove2.me/theorems/971b92b1-2ba7-5c65-97da-6d89ee827186
-- title:
--   Core A: adj closed
-- statement:
--   The Core A construction uses the adj closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/DiagApply.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/DiagApply.lean#L11-L35

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SupPerp
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_DiagApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}

theorem PositivityTheory.Rg.Sw.LC.CoreA.adj_closed (h : PosH φ) {ι : Type} (T : ι → Module.End ℂ V)
    (hT : ∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) :
    ∀ s ∈ Algebra.adjoin ℂ (Set.range T), ∃ s' ∈ Algebra.adjoin ℂ (Set.range T), ∀ v w, φ (s v) w = φ v (s' w) := by sorry
