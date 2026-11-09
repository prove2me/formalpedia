-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_estimator_unbiased
-- name    : QuantumOnePCA369.PauliPCA.estimator_unbiased
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:55.588171+00:00
-- url     : https://prove2.me/theorems/c3d1b902-bf4e-44a5-a5c6-3ff880061079
-- title:
--   Lemma 3.5 — the per-copy Pauli estimator is unbiased for the compressed block
-- statement:
--   Let $\rho$ be an $n$-qubit state, $n=\ell+m$, and run Algorithm 3 with matrices $\tilde U_s$. For every round $r$, every copy index $j\in\{0,1\}^\ell$ and every prefix $s\in\{0,1\}^\ell$,
--   $$\mathbb E\Big[\sum_{x\in\mathbb F_2^m}\mathbb 1\{s^{(r,x,j)}=s\}\cdot O^{(r,x,j)}\,\pi_s^{(r)}(x)\Big]=(\langle s|\otimes\tilde U_s^\dagger)\,\rho\,(|s\rangle\otimes\tilde U_s),$$
--   the expectation being over $A_r,c_r$ and the measurement outcomes, drawn as in Algorithm 3, and $\pi_s^{(r)}$ the output of Algorithm 2.
--
--   Averaging over $j$ and summing shows that each round's estimate $\hat\rho_s^{(r)}$ is unbiased; this is the mean the Lepskii estimator targets in Lemma 3.7.
--
--   **Formalization Note** The expectation is taken under the law of the whole Algorithm 3 protocol (all rounds), with uniform randomness and independent Born-rule outcomes; the integrand depends on round $r$ only.
--
--   Differences from the source:
--   - generalization: partial unitaries Ũ_s with k_0 ≤ 2k, and Algorithm 3's parameters → arbitrary complex 2^m × k_0 matrices Ũ_s and arbitrary k, M, p, δ (which only fix R); reason: unbiasedness is linear in π_s and holds without orthonormality; the source's case is a special case
--   - encoding: measure the last n − ℓ qubits in the σ_{x,A_r x+c_r} basis and observe O ∈ {±1} → each qubit with label (x_j, z_j) = (1,0), (1,1), (0,1) is measured in X, Y, Z; at (0,0) it is measured in Z and its bit ignored; O is the product of (−1)^{y_j} over the non-identity sites; reason: this is the Pauli basis measurement of σ_{x,z} = ⊗_j i^{x_j z_j} X^{x_j} Z^{z_j} (p. 6)
--   - encoding: prefix s ∈ {0,1}^ℓ on the first ℓ qubits, Ũ_s of size 2^{n−ℓ} × k_0 → separate prefix and suffix lengths ℓ and m with ℓ + m = n; Ũ_s : 2^m × k_0; reason: m = n − ℓ without natural-number subtraction
--   - encoding: E over s^{(r,x,j)}, O^{(r,x,j)}, A_r, c_r → expectation under the outcome law of the Algorithm 3 protocol (uniform randomness, independent Born outcomes); reason: the integrand depends only on the variables the source names
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 9, Lemma 3.5; Algorithm 3, p. 10

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_ProjectedPauli
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
import Definitions.Def_QuantumOnePCA369_PauliPCA_SubspaceTomography

namespace QuantumOnePCA369.PauliPCA

theorem estimator_unbiased (ch : SpectralChooser) (n ℓ m k₀ k M : ℕ) (p δ : ℝ)
    (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ) (ρ : Matrix (Bits n) (Bits n) ℂ)
    (hn : ℓ + m = n) (hρ : IsDensity ρ) (r : Fin (alg3R ℓ k M p)) (j s : Bits ℓ) :
    (alg3Protocol ch n ℓ m k₀ k M p δ U).expect ρ
        (fun (rnd : Fin (alg3R ℓ k M p) → SymF2 m × Bits m)
            (out : Fin (alg3R ℓ k M p) × Bits m × Bits ℓ → Bits n) =>
          ∑ x : Bits m,
            ((if prefixBits ℓ (out (r, x, j)) = s then (1 : ℂ) else 0) *
                pauliOutcome ℓ m x ((rnd r).1.1.mulVec x + (rnd r).2) (out (r, x, j))) •
              (alg2 ℓ m k₀ (alg3R ℓ k M p) (fun r' => (rnd r').1) (fun r' => (rnd r').2) U).val
                r s x) =
      (U s).conjTranspose * prefixBlock ℓ m ρ s * U s := by sorry

end QuantumOnePCA369.PauliPCA
