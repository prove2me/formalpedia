-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_mem_perp
-- name    : PositivityTheory.Rg.Sw.LC.CoreA.PosH.mem_perp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:58:30.4226+00:00
-- url     : https://prove2.me/theorems/1b3a89b8-7b6a-4471-b801-77d0ff2528f5
-- title:
--   Pos H: mem perp
-- statement:
--   The Pos H construction uses the mem perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ZeroRight.lean#L65-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ZeroRight.lean#L65-L65

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

theorem PositivityTheory.Rg.Sw.LC.CoreA.PosH.mem_perp (W : Submodule ℂ V) (v : V) : v ∈ h.perp W ↔ ∀ w ∈ W, φ w v = 0 := by sorry
