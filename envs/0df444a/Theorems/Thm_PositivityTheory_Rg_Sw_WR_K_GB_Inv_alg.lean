-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_alg
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.Inv.alg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:50:25.000194+00:00
-- url     : https://prove2.me/theorems/a36ded51-283a-4eb5-a814-64970209c48d
-- title:
--   Inv: alg
-- statement:
--   The Inv construction uses the alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L149-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L149-L221

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv

theorem PositivityTheory.Rg.Sw.WR.K.GB.Inv.alg (A B : Matrix (Fin n) (Fin n) ℂ) (Φ : (Fin n → Fin n × Fin n) → ℂ)
    (hΦ : ∀ r (π : Equiv.Perm (Fin n)), Φ (r ∘ π) = Φ r) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ r : Fin n → Fin n × Fin n, (∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r =
      A.det * B.det * ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (fun t => (σ t, t)) := by sorry
