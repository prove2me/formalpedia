-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_sum_perm_eq_det
-- name    : PositivityTheory.Rg.Sw.WR.D.sum_perm_eq_det
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:26.895854+00:00
-- url     : https://prove2.me/theorems/1a314db6-50ae-40ae-92df-2a0f0e4cdd0a
-- title:
--   D: sum perm eq det
-- statement:
--   The D construction uses the sum perm eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivF.lean#L119-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivF.lean#L119-L135

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

theorem PositivityTheory.Rg.Sw.WR.D.sum_perm_eq_det :
    ∑ σ : Equiv.Perm (Fin n), MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod)
      = MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε := by sorry
