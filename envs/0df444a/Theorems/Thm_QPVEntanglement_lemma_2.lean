-- Prove2me | Theorems.Thm_QPVEntanglement_lemma_2
-- name    : QPVEntanglement.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:33:33.004213+00:00
-- url     : https://prove2.me/theorems/683bff80-01a7-4359-887e-3bdc4f39a32c
-- title:
--   Lemma 2 — quantum-register dimension bound
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $\rho_{A_1A_2}=\sum_cp_c|c\rangle\langle c|_C\otimes\rho^{(c)}_{A_1'A_2}$ with $A_1=C\otimes A_1'$, $C$ classical and $A_1'$ a quantum register. Then
--
--   $$E_{sq}(A_1:A_2)_\rho\le\log_2\dim(\mathcal H_{A_1'});$$
--
--   in particular $E_{sq}(A_1:A_2)_\rho\le Q$ if $A_1'$ consists of $Q$ qubits, and the same holds with $A_1$ and $A_2$ interchanged. It converts the entanglement lower bound into a lower bound on qubits, however large the classical record.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
--   - encoding: dim(H_A′1); A′1 consists of Q qubits → Fintype.card of the basis type; Fin Q → Fin 2; reason: the dimension of a finite-dimensional register is the size of its basis
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 2, p.27; proof p.63

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe

set_option autoImplicit false

universe u v w

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Lemma 2 (Quantum-Register Dimension Bound)**, p.27 (proof p.63). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Lemma 2, p.27.

Let `ρ_{A₁A₂} = Σ_c p_c |c⟩⟨c|_C ⊗ ρ^{(c)}_{A₁'A₂}` with `A₁ = C ⊗ A₁'`, `C` classical. Then
(1) `E_sq(A₁ : A₂)_ρ ≤ log₂ dim H_{A₁'}`; (2) if `A₁'` consists of `Q` qubits,
`E_sq(A₁ : A₂)_ρ ≤ Q`; (3) the same holds with `A₁` and `A₂` interchanged.

**Formalization Note.** The state is `recordOnLeft p ρ` on `(C × A₁') × A₂` (resp.
`recordOnRight` on `A₁ × (C × A₂')`); `dim H_{A₁'}` is the cardinality of the basis type; a
`Q`-qubit register is `Fin Q → Fin 2`. -/
theorem lemma_2 :
    (∀ {C : Type u} {A1 : Type v} {A2 : Type w} [Fintype C] [DecidableEq C] [Fintype A1] [DecidableEq A1] [Fintype A2]
      [DecidableEq A2] (p : C → ℝ) (ρ : C → Matrix (A1 × A2) (A1 × A2) ℂ),
      IsProbVec p → (∀ c, IsDensity (ρ c)) →
        squashed (recordOnLeft p ρ) ≤ Real.logb 2 (Fintype.card A1)) ∧
    (∀ {C : Type u} {A2 : Type w} [Fintype C] [DecidableEq C] [Fintype A2] [DecidableEq A2] (Q : ℕ)
      (p : C → ℝ) (ρ : C → Matrix ((Fin Q → Fin 2) × A2) ((Fin Q → Fin 2) × A2) ℂ),
      IsProbVec p → (∀ c, IsDensity (ρ c)) → squashed (recordOnLeft p ρ) ≤ Q) ∧
    (∀ {C : Type u} {A1 : Type v} {A2 : Type w} [Fintype C] [DecidableEq C] [Fintype A1] [DecidableEq A1] [Fintype A2]
      [DecidableEq A2] (p : C → ℝ) (ρ : C → Matrix (A1 × A2) (A1 × A2) ℂ),
      IsProbVec p → (∀ c, IsDensity (ρ c)) →
        squashed (recordOnRight p ρ) ≤ Real.logb 2 (Fintype.card A2)) := by sorry

end QPVEntanglement
