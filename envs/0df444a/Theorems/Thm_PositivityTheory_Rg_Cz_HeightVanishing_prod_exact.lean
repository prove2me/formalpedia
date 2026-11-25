-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_prod_exact
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.prod_exact
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:49.371816+00:00
-- url     : https://prove2.me/theorems/2741b8cc-f200-4346-9241-36b0d300e926
-- title:
--   Height Vanishing: prod exact
-- statement:
--   The Height Vanishing construction uses the prod exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L298-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L298-L345

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)

theorem PositivityTheory.Rg.Cz.HeightVanishing.prod_exact {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
    (hψ1 : ∀ a b : Fin n, (a : ℕ) + 1 = b → ψ a b ≠ 0)
    (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
    (L : List ℂ) : ∀ j i : Fin n, (j : ℕ) + L.length = i → ∃ c : ℂ, c ≠ 0 ∧ ∀ v,
      ℓ ((L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod (Pi.single (fun _ => j) v) (fun _ => i)) =
        c * ℓ v := by sorry
