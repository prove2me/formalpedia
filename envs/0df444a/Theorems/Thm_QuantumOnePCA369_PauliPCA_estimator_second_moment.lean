-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_estimator_second_moment
-- name    : QuantumOnePCA369.PauliPCA.estimator_second_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:13.715815+00:00
-- url     : https://prove2.me/theorems/4b7bbce8-f13a-473e-a77f-4cf683e7445c
-- title:
--   Lemma 3.6 — second moment of a round's estimate: $\|\mathbb E\hat\rho_s^{(r)}\hat\rho_s^{(r)}\|_\infty\le3k(\cdot)$
-- statement:
--   Let $\rho$ be an $n$-qubit state, $n=\ell+m$, $k\ge1$, and let each $\tilde U_s$ be a $2^m\times k_0$ isometry with $k_0\le2k$. For every round $r$ and prefix $s$ of Algorithm 3,
--   $$\big\|\mathbb E\,\hat\rho_s^{(r)}\hat\rho_s^{(r)}\big\|_\infty\le3k\Big(\operatorname{tr}(|s\rangle\langle s|\otimes I\rho)^2+\frac{\operatorname{tr}(|s\rangle\langle s|\otimes I\rho)}{2^\ell}\Big),$$
--   where $\hat\rho_s^{(r)}=\sum_x\hat\rho_s^{(r,x)}$ is the round-$r$ estimate of lines 13–14 and the expectation is over the randomness and outcomes of Algorithm 3.
--
--   This is the uncentered second-moment bound that places $\beta_s^2=3k(\mathrm{tr}^2+\mathrm{tr}/2^\ell)$ inside Lepskii's window $[\beta^2_{\min},\beta^2_{\max}]$ whenever the prefix mass is at least $p_\ell$.
--
--   **Formalization Note** $\hat\rho_s^{(r)}$ is the intermediate value computed by the program of Algorithm 3 (lines 6–14); the expectation is under the law of the whole protocol.
--
--   Differences from the source:
--   - encoding: partial unitaries Ũ_s of dimension 2^{n−ℓ} × k_0 (k_0 ≤ 2k), k a subspace dimension → Ũ_s^† Ũ_s = I, k_0 ≤ 2k, 1 ≤ k; reason: these are Algorithm 3's input conventions; k ≥ 1 is the dimension convention used by 3k ≥ 2k + 1
--   - encoding: prefix s ∈ {0,1}^ℓ on the first ℓ qubits, Ũ_s of size 2^{n−ℓ} × k_0 → separate prefix and suffix lengths ℓ and m with ℓ + m = n; Ũ_s : 2^m × k_0; reason: m = n − ℓ without natural-number subtraction
--   - encoding: E ρ̂_s^{(r)} ρ̂_s^{(r)} → the uncentered second moment under the outcome law of the Algorithm 3 protocol; reason: the printed quantity, with the expectation made explicit
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 10, Lemma 3.6 (proof pp. 10–11); Algorithm 3, p. 10

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
import Definitions.Def_QuantumOnePCA369_PauliPCA_SubspaceTomography

namespace QuantumOnePCA369.PauliPCA

theorem estimator_second_moment (ch : SpectralChooser) (n ℓ m k₀ k M : ℕ) (p δ : ℝ)
    (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ) (ρ : Matrix (Bits n) (Bits n) ℂ)
    (hn : ℓ + m = n) (hρ : IsDensity ρ) (hk : 1 ≤ k) (hk₀ : k₀ ≤ 2 * k)
    (hU : ∀ s, IsIsometry (U s)) (r : Fin (alg3R ℓ k M p)) (s : Bits ℓ) :
    opNorm ((alg3Protocol ch n ℓ m k₀ k M p δ U).expect ρ
        (fun (rnd : Fin (alg3R ℓ k M p) → SymF2 m × Bits m)
            (out : Fin (alg3R ℓ k M p) × Bits m × Bits ℓ → Bits n) =>
          (alg3Rounds n ℓ m k₀ (alg3R ℓ k M p) U rnd (fun r' x j => out (r', x, j))).val r s *
            (alg3Rounds n ℓ m k₀ (alg3R ℓ k M p) U rnd (fun r' x j => out (r', x, j))).val r s)) ≤
      3 * k * (prefixMass ℓ m ρ s ^ 2 + prefixMass ℓ m ρ s / 2 ^ ℓ) := by sorry

end QuantumOnePCA369.PauliPCA
