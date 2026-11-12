-- Prove2me | Theorems.Thm_QPVEntanglement_theorem_6
-- name    : QPVEntanglement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:33:18.691358+00:00
-- url     : https://prove2.me/theorems/bc4617d3-edfd-4df1-801f-6c7490f4a4b7
-- title:
--   Theorem 6 — entanglement consumed by transferring entangled Bell halves
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $O=O_1\cdots O_k$ be $k$ qubits and $\rho_{OA_1A_2}=\sum_cp_c|c\rangle\langle c|_C\otimes|\psi_c\rangle\langle\psi_c|_{OA_1'A_2}$ with $A_1=C\otimes A_1'$. Suppose:
--
--   1. there are $k$ local unitaries $U_j=\sum_c|c\rangle\langle c|_C\otimes U^{(c)}_j$ on $A_1$ (not scrambling the flag) with $\frac1k\sum_jF(\tilde\rho^{(j)}_{O_jR_j},\Phi^+)\ge1-\epsilon^2$, $0\le\epsilon\le3/4$;
--   2. an LOCC channel $\Lambda$ across $A_1:A_2$ is applied, $\tau=(\mathrm{id}_O\otimes\Lambda)(\rho)$;
--   3. there are $k$ local unitaries $V_j$ on $A_2$ with $\frac1k\sum_jF(\tilde\tau^{(j)}_{O_jW_j},\Phi^+)\ge1-(\epsilon')^2$, $0\le\epsilon'\le1/2$.
--
--   Then the squashed entanglement consumed across $A_1:A_2$ satisfies
--
--   $$\Delta E_{sq}=E_{sq}(A_1:A_2)_\rho-E_{sq}(A_1:A_2)_\tau\ge k\big[1-2g(\epsilon)-f(\epsilon')\big].$$
--
--   It is the entanglement-consumption theorem behind the security proof.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
--   - encoding: target register R_j ⊂ A′1 (resp. W_j in A2) and the recovered marginal ρ̃^(j)_{OjRj} → R_j the ℂ² factor of a fixed identification A′1 ≃ ℂ² ⊗ P_j; ρ̃ the two-qubit partial trace `pairMarginal`; F(·, Φ⁺) the overlap ⟨Φ⁺|·|Φ⁺⟩; reason: a qubit subregister is a ℂ² tensor factor; F is squared Uhlmann fidelity, which against the pure Φ⁺ is the overlap (p.26)
--   - encoding: an LOCC channel Λ across A1 : A2 → `IsLOCCAcross Λ`: after relabelling basis indices, a published `FiniteLOCC` protocol (finite adaptive rounds, complete local Kraus instruments); output registers arbitrary; reason: standard finite-round LOCC, the class of fact (ii), p.26
--   - encoding: (1/k) Σ_{j=1}^k …, k qubits → hypothesis 0 < k; reason: excludes only the undefined average at k = 0
--   - reading: ΔE_sq (squashed entanglement consumed across A1 : A2) → E_sq(A1:A2)_ρ − E_sq(A1:A2)_τ; reason: written out so in (94), p.72, and in Corollary 2 (22)
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Theorem 6, eqs. (10)–(13), p.34; proof p.69

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe
import Definitions.Def_QPVEntanglement_IsLOCCAcross

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Theorem 6 (Entanglement Consumed due to Transferring Entangled Bell Halves)**, p.34
(proof p.69). Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), Theorem 6, eqs. (10)–(13), p.34.

Let `O = O₁⋯O_k` be `k` qubits and `ρ_{OA₁A₂} = Σ_c p_c |c⟩⟨c|_C ⊗ |ψ_c⟩⟨ψ_c|_{OA₁'A₂}` with
`A₁ = C ⊗ A₁'`. Suppose flag-respecting local unitaries `U_j = Σ_c |c⟩⟨c|_C ⊗ U^{(c)}_j` on
`A₁` give `(1/k) Σ_j F(ρ̃^{(j)}_{O_jR_j}, Φ⁺) ≥ 1 − ϵ²`, `0 ≤ ϵ ≤ 3/4`; an LOCC channel `Λ`
across `A₁ : A₂` gives `τ = (id_O ⊗ Λ)(ρ)`; and local unitaries `V_j` on `A₂` give
`(1/k) Σ_j F(τ̃^{(j)}_{O_jW_j}, Φ⁺) ≥ 1 − (ϵ')²`, `0 ≤ ϵ' ≤ 1/2`. Then
`ΔE_sq = E_sq(A₁ : A₂)_ρ − E_sq(A₁ : A₂)_τ ≥ k[1 − 2g(ϵ) − f(ϵ')]`.

**Formalization Note.** `R_j` (resp. `W_j`) is the `ℂ²` factor of a fixed identification of
`A₁'` (resp. of `Λ`'s `A₂`-side output `B₂`) with `ℂ² ⊗ P_j` (resp. `ℂ² ⊗ Q_j`);
`ρ̃^{(j)}` and `τ̃^{(j)}` are the two-qubit marginals of `U_jρU_j†` and `V_jτV_j†`; `F` is
the overlap with `Φ⁺`. `Λ`'s output registers `B₁, B₂` are arbitrary. `0 < k` excludes only
the undefined average `(1/0)·Σ`. -/
theorem theorem_6 {k : ℕ} {C A1 A2 B1 B2 : Type*} [Fintype C] [DecidableEq C] [Fintype A1]
    [DecidableEq A1] [Fintype A2] [DecidableEq A2] [Fintype B1] [DecidableEq B1] [Fintype B2]
    [DecidableEq B2] {P Q : Fin k → Type*} [∀ j, Fintype (P j)] [∀ j, Fintype (Q j)]
    (hk : 0 < k) (p : C → ℝ) (ψ : C → (Fin k → Fin 2) × (A1 × A2) → ℂ) (hp : IsProbVec p)
    (hψ : ∀ c, IsUnitVec (ψ c))
    (U : Fin k → C → Matrix.unitaryGroup A1 ℂ) (eR : (j : Fin k) → A1 ≃ Fin 2 × P j)
    (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 3 / 4)
    (hinit : 1 - ε ^ 2 ≤ (1 / (k : ℝ)) * ∑ j, bellOverlap (pairMarginal (qubitAt j)
      (extLeft (extFlag (C := C) (eR j)))
      (Matrix.kronecker (1 : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
          (Matrix.kronecker (flagControlled fun c => (U j c : Matrix A1 A1 ℂ)) (1 : Matrix A2 A2 ℂ)) *
        flaggedState p ψ *
        (Matrix.kronecker (1 : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
          (Matrix.kronecker (flagControlled fun c => (U j c : Matrix A1 A1 ℂ)) (1 : Matrix A2 A2 ℂ)))ᴴ)))
    (Λ : QAlgorithms.Superop ((C × A1) × A2) (B1 × B2)) (hΛ : IsLOCCAcross Λ)
    (V : Fin k → Matrix.unitaryGroup B2 ℂ) (eW : (j : Fin k) → B2 ≃ Fin 2 × Q j)
    (ε' : ℝ) (hε' : 0 ≤ ε' ∧ ε' ≤ 1 / 2)
    (hfin : 1 - ε' ^ 2 ≤ (1 / (k : ℝ)) * ∑ j, bellOverlap (pairMarginal (qubitAt j)
      (extRight (A := B1) (eW j))
      (Matrix.kronecker (1 : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
          (Matrix.kronecker (1 : Matrix B1 B1 ℂ) (V j : Matrix B2 B2 ℂ)) *
        QAlgorithms.idTensorSuperop Λ (flaggedState p ψ) *
        (Matrix.kronecker (1 : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
          (Matrix.kronecker (1 : Matrix B1 B1 ℂ) (V j : Matrix B2 B2 ℂ)))ᴴ))) :
    (k : ℝ) * (1 - 2 * gFun ε - fFun ε') ≤
      squashed (QAlgorithms.traceLeft (flaggedState p ψ)) -
        squashed (QAlgorithms.traceLeft (QAlgorithms.idTensorSuperop Λ (flaggedState p ψ))) := by sorry

end QPVEntanglement
