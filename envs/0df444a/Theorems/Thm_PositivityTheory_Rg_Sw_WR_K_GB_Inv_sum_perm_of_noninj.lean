-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_sum_perm_of_noninj
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.Inv.sum_perm_of_noninj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:12.787126+00:00
-- url     : https://prove2.me/theorems/862eefa2-2597-4197-bc3d-bf76d3445c75
-- title:
--   Inv: sum perm of noninj
-- statement:
--   The Inv construction uses the sum perm of noninj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L131-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L131-L142

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.Inv.sum_perm_of_noninj {α : Type*} [AddCommMonoid α] (h : (Fin n → Fin n) → α)
    (h0 : ∀ c, ¬ Function.Injective c → h c = 0) :
    ∑ c : Fin n → Fin n, h c = ∑ π : Equiv.Perm (Fin n), h π := by sorry
