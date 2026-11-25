-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_crd_apply
-- name    : PositivityTheory.Rg.Sw.WR.G.crd_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:29.25345+00:00
-- url     : https://prove2.me/theorems/6f8b10a0-4eeb-41c9-97ed-5b00a5c85a3f
-- title:
--   G: crd apply
-- statement:
--   The G construction uses the crd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GWickA.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GWickA.lean#L23-L25

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

theorem PositivityTheory.Rg.Sw.WR.G.crd_apply (k : Fin m × Fin n × Bool) (v : Fin m → Fin n → ℂ) :
    crd k v = if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by sorry
