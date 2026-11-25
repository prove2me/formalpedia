-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_ad
-- name    : PositivityTheory.Rg.Cz.TGK.actT_ad
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:40.446091+00:00
-- url     : https://prove2.me/theorems/80262844-f9ff-5f89-a011-b7007801ea54
-- title:
--   TGK: act T ad
-- statement:
--   The TGK construction uses the act T ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L204-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L204-L222

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.actT_ad {ι Γ : Type} [DecidableEq ι] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M)
    (hu : ∀ τ γ, κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ γ τ a b, ρ γ * E τ a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E τ c d) * ρ γ)
    (γ : Γ) (τ : ι) (a b : Fin n) :
    actT lab κ ρ γ * tE (fib lab τ) (E τ) a b =
      (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • tE (fib lab τ) (E τ) c d) * actT lab κ ρ γ := by sorry
