-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_anti_id
-- name    : PositivityTheory.Rg.Cz.CtrX.actT_anti_id
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:29.942898+00:00
-- url     : https://prove2.me/theorems/5c4d7ef2-ee6d-4afa-abd7-5d0a7d22bc14
-- title:
--   Ctr X: act T anti id
-- statement:
--   The Ctr X construction uses the act T anti id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractD.lean#L50-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractD.lean#L50-L81

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.CtrX.actT_anti_id {ι Γ : Type} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (f : TV n M (Fin n)) (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) :
    actT (fun _ : Fin n => τ) κ ρ γ f id = (κ τ γ).det • ρ γ (f id) := by sorry
