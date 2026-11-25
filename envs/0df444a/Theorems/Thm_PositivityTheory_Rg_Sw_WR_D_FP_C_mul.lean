-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_FP_C_mul
-- name    : PositivityTheory.Rg.Sw.WR.D.FP_C_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:11.475797+00:00
-- url     : https://prove2.me/theorems/d0798ff4-712e-4815-8b63-38ee70419565
-- title:
--   D: FP C mul
-- statement:
--   The D construction uses the FP C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivF.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivF.lean#L90-L96

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}

theorem PositivityTheory.Rg.Sw.WR.D.FP_C_mul (a : ℂ) (P : PX m n) :
    FP ε c t (MvPolynomial.C a * P) = a • FP ε c t P := by sorry
