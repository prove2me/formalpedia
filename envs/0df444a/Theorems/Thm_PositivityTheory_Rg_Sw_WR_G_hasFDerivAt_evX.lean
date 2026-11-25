-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_hasFDerivAt_evX
-- name    : PositivityTheory.Rg.Sw.WR.G.hasFDerivAt_evX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:42.286458+00:00
-- url     : https://prove2.me/theorems/5cdcc005-dc23-4f14-b6b4-7b5d7f2061ef
-- title:
--   G: has FDeriv At ev X
-- statement:
--   The G construction uses the has FDeriv At ev X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GWickA.lean#L40-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GWickA.lean#L40-L65

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.G.hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (evX P) (dEv P x) x := by sorry
