-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_crd_wirt
-- name    : PositivityTheory.Rg.Sw.WR.G.crd_wirt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:07:59.037154+00:00
-- url     : https://prove2.me/theorems/7f8487a0-ea78-5009-8160-b7ae63482907
-- title:
--   G: crd wirt
-- statement:
--   The G construction uses the crd wirt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/EvXPderivPhiP.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/EvXPderivPhiP.lean#L49-L59

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

theorem PositivityTheory.Rg.Sw.WR.G.crd_wirt (a : Fin m) (j : Fin n) (k : Fin m × Fin n × Bool) :
    crd k (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * crd k (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      if k = (a, j, false) then 2 else 0 := by sorry
