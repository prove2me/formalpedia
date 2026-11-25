-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_dEv_wirt
-- name    : PositivityTheory.Rg.Sw.WR.G.dEv_wirt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:57.526257+00:00
-- url     : https://prove2.me/theorems/4d5667f0-562f-5b16-a0c3-71237f9a7bd2
-- title:
--   G: d Ev wirt
-- statement:
--   The G construction uses the d Ev wirt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/EvXPderivPhiP.lean#L61-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/EvXPderivPhiP.lean#L61-L75

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_EvXPderivPhiP
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.G.dEv_wirt (P : PX m n) (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    dEv P x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * dEv P x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      2 * evX (pderiv (a, j, false) P) x := by sorry
