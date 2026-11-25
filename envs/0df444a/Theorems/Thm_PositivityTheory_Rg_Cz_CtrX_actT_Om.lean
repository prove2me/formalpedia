-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_Om
-- name    : PositivityTheory.Rg.Cz.CtrX.actT_Om
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:59.114268+00:00
-- url     : https://prove2.me/theorems/8e6ce5a4-a311-4689-a5a5-84978dd946f4
-- title:
--   Ctr X: act T Om
-- statement:
--   The Ctr X construction uses the act T Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean#L109-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean#L109-L160

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
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

theorem PositivityTheory.Rg.Cz.CtrX.actT_Om {ι Γ : Type} {m : ℕ} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M)
    (ρ : Γ → Module.End ℂ M) (γ : Γ) (hu : κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ a b, ρ γ * E a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E c d) * ρ γ) (j : Fin m)
    (f : TV n M (Fin m)) :
    actT (fun _ : Fin m => τ) κ ρ γ (Om E j f) = Om E j (actT (fun _ : Fin m => τ) κ ρ γ f) := by sorry
