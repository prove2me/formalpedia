-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_core
-- name    : PositivityTheory.Rg.Cz.CtrX.core
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:54:07.209421+00:00
-- url     : https://prove2.me/theorems/6c8978bc-ec3d-4d4b-8172-aa9fd1ffce7b
-- title:
--   Ctr X: core
-- statement:
--   The Ctr X construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractB.lean#L46-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractB.lean#L46-L201

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractB
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

theorem PositivityTheory.Rg.Cz.CtrX.core (hQ : QdetFacts) (hW : WallAlg) (hT : TensorGK) (hL : LieInv)
    {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
    {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (τ0 : ι)
    {M0 : Type} [AddCommGroup M0] [Module ℂ M0] (q : M →ₗ[ℂ] M0) (F1 F2 : Fin n → Fin n → Module.End ℂ M0)
    (s : ℂ) (hF1 : GlRel F1) (hF2 : GlRel F2) (hc : ∀ a b c d, Commute (F1 a b) (F2 c d))
    (hs1 : HasChar F1 fun _ => s) (hs2 : HasChar F2 fun _ => s)
    (hq1 : ∀ a b, q ∘ₗ E τ0 a b = F1 a b ∘ₗ q) (hq2 : ∀ a b, q ∘ₗ E (bar τ0) a b = F2 a b ∘ₗ q)
    (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (c : ι → ℤ) (ζ : TV n M (Fin m))
    (hζ : ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ ζ = (∏ τ, (κ τ γ).det ^ c τ) • ζ) (hz : ∃ I, q (ζ I) ≠ 0) :
    ∃ m2 < m, ∃ ζ2 : TV n M (Fin m2), (∀ γ, actT (fun _ : Fin m2 => τ0) κ ρ γ ζ2 =
      (∏ τ, (κ τ γ).det ^ (Function.update c τ0 (c τ0 - 1)) τ) • ζ2) ∧ ∃ I, q (ζ2 I) ≠ 0 := by sorry
