-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_term
-- name    : PositivityTheory.Rg.Cz.YoungTableau.term
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:35.117804+00:00
-- url     : https://prove2.me/theorems/365e2a6f-9f29-4a2d-b2c3-ce610745d9c6
-- title:
--   Young Tableau: term
-- statement:
--   The Young Tableau construction uses the term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoung.lean#L26-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoung.lean#L26-L91

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoung
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
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [DecidableEq ι]
  {Q : Type} [Fintype Q] [DecidableEq Q] {N : ℕ} {C : Type} [DecidableEq C]

theorem PositivityTheory.Rg.Cz.YoungTableau.term (tl : Fin N → ι) (col : Q ⊕ (Fin N ⊕ Fin N) → C) (b : Q ⊕ (Fin N ⊕ Fin N) → Fin n)
    (hT : IsTab col b) (h1 : ∀ p k, col (.inl p) ≠ col (.inr k)) (h2 : ∀ k k', col (.inr (.inl k)) ≠ col (.inr (.inr k')))
    (ξ : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (σ : Equiv.Perm (Fin N)) :
    alt (colG col) ξ (b ∘ dbl σ) =
      ((sg (col ∘ inF Q N) (b ∘ inF Q N) ((b ∘ inF Q N) ∘ σ) * sg (col ∘ inS Q N) (b ∘ inS Q N) ((b ∘ inS Q N) ∘ σ) : ℤ) : ℂ)
        • alt (colG col) ξ b := by sorry
