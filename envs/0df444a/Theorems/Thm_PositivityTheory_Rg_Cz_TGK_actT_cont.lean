-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_cont
-- name    : PositivityTheory.Rg.Cz.TGK.actT_cont
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:50.958586+00:00
-- url     : https://prove2.me/theorems/f1592031-2e1d-4528-aab2-a7063dcc16cf
-- title:
--   TGK: act T cont
-- statement:
--   The TGK construction uses the act T cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKB.lean#L32-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKB.lean#L32-L53

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKB
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

theorem PositivityTheory.Rg.Cz.TGK.actT_cont {ι Γ : Type} [TopologicalSpace Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ i j, Continuous fun γ => κ τ γ i j)
    (hc : ∀ y (lam : M →ₗ[ℂ] ℂ), Continuous fun γ => lam (ρ γ y)) (y : TV n M P) (lam : TV n M P →ₗ[ℂ] ℂ) :
    Continuous fun γ => lam (actT lab κ ρ γ y) := by sorry
