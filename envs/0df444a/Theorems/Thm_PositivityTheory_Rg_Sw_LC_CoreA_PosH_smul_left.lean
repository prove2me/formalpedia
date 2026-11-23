-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_smul_left
-- name    : PositivityTheory.Rg.Sw.LC.CoreA.PosH.smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:54.664418+00:00
-- url     : https://prove2.me/theorems/c21e50a8-2d9e-452b-b4b8-9f39b8c22763
-- title:
--   Pos H: smul left
-- statement:
--   The Pos H construction uses the smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ZeroRight.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ZeroRight.lean#L34-L35

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

theorem PositivityTheory.Rg.Sw.LC.CoreA.PosH.smul_left (v w : V) (r : ℂ) : φ (r • v) w = star r * φ v w := by sorry
