-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TrOf_transfer
-- name    : PositivityTheory.Rg.Cz.TrOf.transfer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:48:31.114632+00:00
-- url     : https://prove2.me/theorems/29042e89-23a0-5c32-9f3c-f24ad1b2aae6
-- title:
--   Tr Of: transfer
-- statement:
--   The Tr Of construction uses the transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L61-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L61-L111

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
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
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

theorem PositivityTheory.Rg.Cz.TrOf.transfer (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℤ) (ℓ : M →ₗ[ℂ] ℂ)
    {C C' : Type} [DecidableEq C] [DecidableEq C'] (col : P → C) (col' : Q → C')
    (hcol : ∀ q q', col' q = col' q' ↔ col (e.symm q) = col (e.symm q')) (b co : P → Fin n)
    (h : ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset Q) E), ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S ≠ 0 ∧
      ∀ u : ℂ, (ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset Q) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co (e.symm p) = k).card : ℂ))) •
          (ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S)) :
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S) := by sorry
