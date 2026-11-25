-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_xJ_nat
-- name    : PositivityTheory.Rg.Cz.SpecA.xJ_nat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:30.64694+00:00
-- url     : https://prove2.me/theorems/4ccd1c9b-eb8d-5ba4-a5ed-0c68c9b5977a
-- title:
--   Spec A: x J nat
-- statement:
--   The Spec A construction uses the x J nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L145-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L145-L151

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}

theorem PositivityTheory.Rg.Cz.SpecA.xJ_nat {m : ℕ} {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) (φ : M₁ →ₗ[ℂ] M₂)
    (h : ∀ a b, φ ∘ₗ E₁ a b = E₂ a b ∘ₗ φ) (j : Fin m) :
    LinearMap.compLeft φ (Fin m → Fin n) ∘ₗ xJ E₁ j = xJ E₂ j ∘ₗ LinearMap.compLeft φ (Fin m → Fin n) := by sorry
