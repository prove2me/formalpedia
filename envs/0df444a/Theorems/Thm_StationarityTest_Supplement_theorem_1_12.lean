-- Prove2me | Theorems.Thm_StationarityTest_Supplement_theorem_1_12
-- name    : StationarityTest.Supplement.theorem_1_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:47:21.1032+00:00
-- url     : https://prove2.me/theorems/5b238f98-7fc8-4587-b0c6-b18b723096ca
-- title:
--   Theorem 1.12 — area law for metastable states: $I(A:\bar A)_\sigma\le 2\beta\|\partial_A H\|+e^{\mu|A|}\varepsilon^\lambda$, independent of $n$
-- statement:
--   Fix integers $k,d,D\ge1$ and $c_{gr}\ge1$. There are constants $C>0$ and $K$ such that for every inverse temperature $\beta>0$ there exist $\mu\le C(1+\beta)^K$ and $\lambda>0$ with $\lambda^{-1}\le C(1+\beta)^K$ for which the following holds for every $n$.
--
--   Let $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ be a $k$-local $(d,D,c_{gr})$ Hamiltonian on $n$ qubits with $|h_\gamma|\le1$, let $A\subseteq[n]$, $\bar A=[n]\setminus A$, let $\varepsilon\ge0$, and let $\sigma$ be a state with
--   $$
--   \|\mathcal L_{H,i}[\sigma]\|_1\le\varepsilon\qquad\text{for each } i\in A .
--   $$
--   Then the quantum mutual information between $A$ and its complement satisfies the approximate thermal area law
--   $$
--   I(A:\bar A)_\sigma\le 2\beta\,\|\partial_A H\|+e^{\mu|A|}\,\varepsilon^{\lambda},
--   $$
--   where $\partial_A H$ is the sum of the Hamiltonian terms incident on both $A$ and $\bar A$ and $\|\cdot\|$ is the operator norm.
--
--   The bound does not depend on the system size $n$, so it is meaningful in the thermodynamic limit; at $\varepsilon=0$ it is the Gibbs-state area law $I\le2\beta\|\partial_A H\|$. Metastability is only required on the sites of $A$.
--
--   **Formalization Note** `poly(β)` is $C(1+\beta)^K$ with $C,K$ depending only on the fixed parameters $k,d,D,c_{gr}$. Entropies use the natural logarithm; $\varepsilon^\lambda$ is the real power ($0^\lambda=0$).
--
--   Differences from the source:
--   - reading: Fix β ≥ 0 → hypothesis 0 < β; reason: L_{H,i} is defined with energy width σ = β⁻¹ (p.17) and does not exist at β = 0; Lean's β⁻¹ = 0 there is a junk value
--   - reading: μ, λ⁻¹ ≤ poly(β) → ∃ C > 0, K depending only on k, d, D, c_gr; for every β > 0 ∃ μ ≤ C(1+β)^K and λ > 0 with λ⁻¹ ≤ C(1+β)^K, the same μ, λ for every n, A, Γ, h, σ, ε; reason: the lattice parameters are fixed constants and the theorem is stated for the thermodynamic limit, so μ, λ may not depend on n, A, σ or ε
--   - encoding: H a lattice Hamiltonian on qubits → H = ham Γ h with q = 1, Γ ⊆ S^k_[n] satisfying IsDDcgr d D cgr Γ, |h_γ| ≤ 1 for γ ∈ Γ, k, d, D ≥ 1, c_gr ≥ 1; reason: the paper's lattice Hamiltonians are the (d, D, c_gr) Hamiltonians (p.14) with coefficients in [−1, 1] (21); 'patch of qubits' fixes q = 1
--   - reading: A ⊆ [n] a patch of qubits → any A : Finset (Fin n); reason: 'patch' is not defined in the paper; the statement says A ⊆ [n] and the proof (App. B.2, 'Fix a set A') uses no other property; the stronger reading
--   - encoding: ε, the bound on ‖L_{H,i}[σ]‖₁ → hypothesis 0 ≤ ε; reason: ε bounds a norm; the condition only excludes negative ε (possible only for A = ∅), where ε^λ is not a real power
--   - encoding: I(A : Ā)_σ, ‖∂_A H‖, ε^λ → mutualInfo A σ in nats, QAlgorithms.specNorm (boundaryHam Γ h A), Real.rpow ε λ; reason: natural logarithm as in (268); ‖·‖ is the operator norm of the sum of the boundary terms; same values
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Theorem 1.12, (12) and footnote 4, p.8 (proof App. B, pp.61–62)

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Supplement_Entropy
import Definitions.Def_StationarityTest_Supplement_Metastable

namespace StationarityTest.Supplement

/-- **Theorem 1.12 (An area law for metastable states)**, p.8 (proof App. B, pp.61–62)
(Bergamaschi, *The stationarity test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Fix
`β ≥ 0`. Let `A ⊆ [n]` be a patch of qubits, `H` a lattice Hamiltonian, and `σ` a state
satisfying `‖L_{H,i}[σ]‖₁ ≤ ε` for each `i ∈ A`. Then
`I(A : Ā)_σ ≤ 2β · ‖∂_A H‖ + e^{μ|A|} ε^λ` (12), where `μ, λ^{−1} ≤ poly(β)` and `∂_A H` are the
Hamiltonian terms incident on `A` and `Ā`.

**Formalization Note.** Qubits: `q = 1`, so a site is a qubit. A lattice Hamiltonian is a
`(d, D, c_gr)` Hamiltonian (p.14) `H = Σ_{γ∈Γ} h_γ P_γ` with `k`-local clauses and `|h_γ| ≤ 1`
(21); `k, d, D ≥ 1`, `c_gr ≥ 1` are fixed and absorbed into the constants. `μ, λ^{−1} ≤ poly(β)`
is read as: `∃ C > 0, K` (depending only on `k, d, D, c_gr`) such that for every `β > 0` there are
`μ ≤ C(1+β)^K` and `λ > 0` with `λ^{−1} ≤ C(1+β)^K`, and these `μ, λ` work for every `n`, every
`A`, every `Γ, h`, every state `σ` and every `ε ≥ 0` (the point of the theorem is that nothing
depends on `n`). `β > 0`, not `β ≥ 0`: `L_{H,i}` has energy width `σ = β^{−1}` (p.17) and is not
defined at `β = 0` (in Lean `β⁻¹ = 0` there, a junk value). `ε ≥ 0` is the range of the error
parameter of a norm bound. `A` is any set of sites ("patch" adds no condition the proof uses);
the hypothesis is only for `i ∈ A`. `I` is in nats, `‖∂_A H‖` is the operator norm of the sum of
the boundary terms, `ε^λ` is `Real.rpow` (`0^λ = 0`). -/
theorem theorem_1_12 : ∀ k d D : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ D → ∀ cgr : ℝ, 1 ≤ cgr →
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ β : ℝ, 0 < β →
    ∃ μ lam : ℝ, μ ≤ C * (1 + β) ^ K ∧ 0 < lam ∧ lam⁻¹ ≤ C * (1 + β) ^ K ∧
    ∀ n : ℕ, ∀ A : Finset (Fin n), ∀ Γ : Finset (KLocal n 1 k), IsDDcgr d D cgr Γ →
    ∀ h : KLocal n 1 k → ℝ, (∀ γ ∈ Γ, |h γ| ≤ 1) →
    ∀ σ : Op n 1, QAlgorithms.IsDensityMatrix σ → ∀ ε : ℝ, 0 ≤ ε →
    (∀ i ∈ A, WildeQIT.traceNorm (lindbladSite (ham Γ h) β i σ) ≤ ε) →
    mutualInfo A σ ≤
      2 * β * QAlgorithms.specNorm (boundaryHam Γ h A) +
        Real.exp (μ * (A.card : ℝ)) * ε ^ lam := by sorry

end StationarityTest.Supplement
