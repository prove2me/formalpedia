-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_letter_zero
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.letter_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:04.431314+00:00
-- url     : https://prove2.me/theorems/df14e9e8-de0e-43d4-a5e1-ef53f0664f32
-- title:
--   Height Vanishing: letter zero
-- statement:
--   The Height Vanishing construction uses the letter zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L117-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L117-L124

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
variable {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
  (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
include hE hψ2 hψ

theorem PositivityTheory.Rg.Cz.HeightVanishing.letter_zero {k : ℕ} (hQ : ∀ (h : ℤ) (A : Module.End ℂ M), A ∈ W E k h → (k : ℤ) < h → ℓ ∘ₗ A = 0)
    (a b : Fin n) (hab : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ≤ 0) {h : ℤ} {A : Module.End ℂ M} (hA : A ∈ W E k h)
    (hk : (k : ℤ) < h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) : ℓ ∘ₗ (E a b * A) = 0 := by sorry
