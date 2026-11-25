-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_mul
-- name    : PositivityTheory.Rg.Cz.TGK.actT_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:37.447718+00:00
-- url     : https://prove2.me/theorems/08eeb1fc-ac1d-5a4e-bf24-a9273457d74b
-- title:
--   TGK: act T mul
-- statement:
--   The TGK construction uses the act T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L176-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L176-L181

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

theorem PositivityTheory.Rg.Cz.TGK.actT_mul {ι Γ : Type} [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ γ δ, κ τ (γ * δ) = κ τ γ * κ τ δ) (hρ : ∀ γ δ, ρ (γ * δ) = ρ γ * ρ δ)
    (γ δ : Γ) : actT lab κ ρ (γ * δ) = actT lab κ ρ γ * actT lab κ ρ δ := by sorry
