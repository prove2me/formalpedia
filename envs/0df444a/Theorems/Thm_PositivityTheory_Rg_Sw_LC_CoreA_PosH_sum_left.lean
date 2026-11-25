-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_sum_left
-- name    : PositivityTheory.Rg.Sw.LC.CoreA.PosH.sum_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:56.387257+00:00
-- url     : https://prove2.me/theorems/a576f3f7-f399-4a15-a35e-bff16a96e6f8
-- title:
--   Pos H: sum left
-- statement:
--   The Pos H construction uses the sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ZeroRight.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ZeroRight.lean#L37-L42

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {φ : V → V → ℂ}
open PositivityTheory.Rg.Sw.LC.CoreA.PosH
variable (h : PosH φ)
include h

theorem PositivityTheory.Rg.Sw.LC.CoreA.PosH.sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (b : ι → V) (w : V) :
    φ (∑ k ∈ s, c k • b k) w = ∑ k ∈ s, star (c k) * φ (b k) w := by sorry
