-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_add_left
-- name    : PositivityTheory.Rg.Sw.LC.CoreA.PosH.add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:06.005627+00:00
-- url     : https://prove2.me/theorems/a1d31aca-ff69-4725-8640-f6d63e1ff04d
-- title:
--   Pos H: add left
-- statement:
--   The Pos H construction uses the add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ZeroRight.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ZeroRight.lean#L31-L32

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

theorem PositivityTheory.Rg.Sw.LC.CoreA.PosH.add_left (v₁ v₂ w : V) : φ (v₁ + v₂) w = φ v₁ w + φ v₂ w := by sorry
