-- Prove2me | Theorems.Thm_QPVEntanglement_lemma_7
-- name    : QPVEntanglement.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:32:35.825902+00:00
-- url     : https://prove2.me/theorems/a538d68b-0a60-48e6-accd-895be53c541d
-- title:
--   Lemma 7 — initial recovery bound
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $O=O_1\cdots O_k$ be $k$ qubits and $\rho_{OA_1A_2}=\sum_cp_c|c\rangle\langle c|_C\otimes|\psi_c\rangle\langle\psi_c|_{OA_1'A_2}$ a classically flagged mixture of pure states with $A_1=C\otimes A_1'$. Suppose for each $j$ there is a local unitary $U_j=\sum_c|c\rangle\langle c|_C\otimes U^{(j)}_c$ on $A_1$ with $U^{(j)}_c$ acting on $A_1'$ and yielding a target qubit $R_j\subset A_1'$, such that the expected trace distance of the conditional recovered states from the Bell state is at most $\delta_j\in[0,1]$: $\mathbb E_c[\mathrm{TD}(\tilde\rho^{(c,j)}_{O_jR_j},\Phi^+)]\le\delta_j$. Then
--
--   $$E_{sq}(OA_1:A_2)_\rho\le E_{sq}(A_1:A_2)_\rho+2\sum_{j=1}^kg_{\mathrm{safe}}(\delta_j).$$
--
--   It is the estimate at the initial recovery endpoint of Theorem 6.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
--   - encoding: target register R_j ⊂ A′1 (resp. W_j in A2) and the recovered marginal ρ̃^(j)_{OjRj} → R_j the ℂ² factor of a fixed identification A′1 ≃ ℂ² ⊗ P_j; ρ̃ the two-qubit partial trace `pairMarginal`; F(·, Φ⁺) the overlap ⟨Φ⁺|·|Φ⁺⟩; reason: a qubit subregister is a ℂ² tensor factor; F is squared Uhlmann fidelity, which against the pure Φ⁺ is the overlap (p.26)
--   - encoding: E_c[TD(ρ̃^(c,j), Φ⁺)] → Σ_c p_c · TD(pair marginal of (I ⊗ U^(j)_c ⊗ I)|ψ_c⟩, Φ⁺); reason: the expectation over the flag distribution of the conditional states
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 7, eqs. (8)–(9), p.33; proof p.66

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe
import Definitions.Def_QPVEntanglement_IsLOCCAcross

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Lemma 7 (Initial Recovery Bound)**, p.33 (proof p.66). Behera–Goyal, arXiv:2609.39234
(sha256 bdf2928d…), Lemma 7, eqs. (8)–(9), p.33.

Let `O = O₁⋯O_k` be `k` qubits and `ρ_{OA₁A₂} = Σ_c p_c |c⟩⟨c|_C ⊗ |ψ_c⟩⟨ψ_c|_{OA₁'A₂}` with
`A₁ = C ⊗ A₁'`. Suppose for each `j` there is a flag-controlled local unitary
`U_j = Σ_c |c⟩⟨c|_C ⊗ U^{(j)}_c` with `U^{(j)}_c` on `A₁'` yielding a target qubit
`R_j ⊂ A₁'`, such that `E_c[TD(ρ̃^{(c,j)}_{O_jR_j}, Φ⁺)] ≤ δ_j ∈ [0,1]`. Then
`E_sq(OA₁ : A₂)_ρ ≤ E_sq(A₁ : A₂)_ρ + 2 Σ_j g_safe(δ_j)`.

**Formalization Note.** `R_j` is the `ℂ²` factor of a fixed identification
`eR j : A₁' ≃ ℂ² ⊗ P_j`; `ρ̃^{(c,j)}_{O_jR_j}` is the two-qubit marginal on `O_j` and `R_j` of
`(I_O ⊗ U^{(j)}_c ⊗ I_{A₂})|ψ_c⟩`; `E_c` is `Σ_c p_c`. -/
theorem lemma_7 {k : ℕ} {C A1 A2 : Type*} [Fintype C] [DecidableEq C] [Fintype A1]
    [DecidableEq A1] [Fintype A2] [DecidableEq A2] {P : Fin k → Type*} [∀ j, Fintype (P j)]
    (p : C → ℝ) (ψ : C → (Fin k → Fin 2) × (A1 × A2) → ℂ) (hp : IsProbVec p)
    (hψ : ∀ c, IsUnitVec (ψ c)) (U : Fin k → C → Matrix.unitaryGroup A1 ℂ)
    (eR : (j : Fin k) → A1 ≃ Fin 2 × P j) (δ : Fin k → ℝ) (hδ : ∀ j, 0 ≤ δ j ∧ δ j ≤ 1)
    (hrec : ∀ j, ∑ c, p c * RandPurIso.Completion.traceDist (pairMarginal (qubitAt j) (extLeft (eR j))
      (pureDensity ((Matrix.kronecker (1 : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
        (Matrix.kronecker (U j c : Matrix A1 A1 ℂ) (1 : Matrix A2 A2 ℂ))).mulVec (ψ c))))
      phiPlus ≤ δ j) :
    squashed (assocL (flaggedState p ψ)) ≤
      squashed (QAlgorithms.traceLeft (flaggedState p ψ)) + 2 * ∑ j, gSafe (δ j) := by sorry

end QPVEntanglement
