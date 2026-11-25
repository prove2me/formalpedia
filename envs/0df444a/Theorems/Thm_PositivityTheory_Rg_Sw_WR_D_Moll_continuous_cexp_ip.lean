-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_cexp_ip
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.continuous_cexp_ip
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:56.216975+00:00
-- url     : https://prove2.me/theorems/07e0e630-95b5-5a97-b748-4f67c9a4b3e9
-- title:
--   Moll: continuous cexp ip
-- statement:
--   The Moll construction uses the continuous cexp ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousCexpIp.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousCexpIp.lean#L16-L17

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ExpCombine
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousCexpIp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem PositivityTheory.Rg.Sw.WR.D.Moll.continuous_cexp_ip (t : ℝ) : Continuous (fun p : E n × E n => Complex.exp (-(Complex.I * t * ip p.1 p.2))) := by sorry
