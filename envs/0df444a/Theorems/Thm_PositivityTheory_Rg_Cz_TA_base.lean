-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_base
-- name    : PositivityTheory.Rg.Cz.TA.base
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:20.225327+00:00
-- url     : https://prove2.me/theorems/bf41e359-8d54-436d-86d1-e63041b78af1
-- title:
--   TA: base
-- statement:
--   The TA construction uses the base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllC.lean#L62-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllC.lean#L62-L87

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllC
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)
omit [Fintype P]

theorem PositivityTheory.Rg.Cz.TA.base (E : ι → Fin n → Fin n → Module.End ℂ M) (l : ι → Fin n → ℤ)
    (hl : ∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) [Fintype P] [IsEmpty P]
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin n) :
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) •
          (ℓ ∘ₗ cA col b ∘ₗ S) := by sorry
