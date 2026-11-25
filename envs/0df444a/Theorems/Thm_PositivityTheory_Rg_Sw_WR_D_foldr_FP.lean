-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_foldr_FP
-- name    : PositivityTheory.Rg.Sw.WR.D.foldr_FP
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:08:04.723288+00:00
-- url     : https://prove2.me/theorems/3127ab33-4244-5f94-ad51-84111f89ea88
-- title:
--   D: foldr FP
-- statement:
--   The D construction uses the foldr FP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivF.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivF.lean#L110-L117

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

theorem PositivityTheory.Rg.Sw.WR.D.foldr_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (σ : Equiv.Perm (Fin n)) (L : List (Fin n)) (P : PX m n) :
    L.foldr (fun k g => Dkl k (σ k) g) (FP ε c t P) =
      FP ε c t ((L.map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod * P) := by sorry
