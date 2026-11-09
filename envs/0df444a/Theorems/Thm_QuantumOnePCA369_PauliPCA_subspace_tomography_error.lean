-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_subspace_tomography_error
-- name    : QuantumOnePCA369.PauliPCA.subspace_tomography_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:45.724669+00:00
-- url     : https://prove2.me/theorems/e472c075-6d17-4113-b477-5138092e18de
-- title:
--   Lemma 3.7 — layer tomography: copies and mass-weighted operator-norm error (corrected: $n$ to $n+1$ in the copy count)
-- statement:
--   Let $0<p_\ell\le1/2$, $n=\ell+m$, $M\ge1$, let $\rho$ be an $n$-qubit state, and let each $\tilde U_s$ be a $2^m\times k_0$ isometry with $k_0\le2k$. There are universal constants $K$ and $C$ such that, for $k\ge K$, Algorithm 3 (with any exact eigensolver):
--
--   1. uses at most $C\,2^n(n+1)M\log(1/p_\ell)$ copies of $\rho$;
--   2. returns Hermitian matrices $\hat\rho_s=(\langle s|\otimes\tilde U_s^\dagger)\rho(|s\rangle\otimes\tilde U_s)+\xi_s$, $s\in\{0,1\}^\ell$, on every run;
--   3. for every $\delta>0$, with probability at least $1-\delta$,
--   $$\sum_{\substack{s\in\{0,1\}^\ell\\ \operatorname{tr}(|s\rangle\langle s|\otimes I\rho)\ge p_\ell}}\frac{\|\xi_s\|_\infty^2}{\operatorname{tr}(|s\rangle\langle s|\otimes I\rho)}\le C\,\frac{k(\ell+1)\log\!\big(k/(p_\ell\delta)\big)}{M}.$$
--
--   This is the per-layer accuracy guarantee that the pruning analysis of Lemma 4.3 sums over layers: prefixes of small mass are ignored, and the others are learned in operator norm relative to their mass.
--
--   **Formalization Note** "$k$ larger than an absolute constant" is a universal $K$ quantified before every instance. The probability is the outcome law of the Algorithm 3 protocol; for $\delta\ge1$ the clause is vacuous.
--
--   Differences from the source:
--   - correction: O(2^n n M log(1/p_ℓ)) copies → ≤ C · 2^n (n+1) M log(1/p_ℓ) copies; reason: at n = 0 (so ℓ = m = 0) Algorithm 3 allocates 2^0·R ≥ 2M·3 > 0 copies while 2^0·0·M·log(1/p_ℓ) = 0; for n ≥ 1, n + 1 ≤ 2n so the bound is unchanged
--   - reading: log(k/p_ℓ δ) → log(k/(p_ℓ·δ)); reason: the proof (p. 11) bounds log(β²max/β²min · 2k·2^ℓ/δ), which has δ in the denominator
--   - encoding: k larger than an absolute constant → ∃ K universal, quantified before every instance, with K ≤ k; reason: the source's absolute constant
--   - encoding: partial unitaries of dimension 2^{n−ℓ} × k_0 (k_0 ≤ 2k), block size M → Ũ_s^† Ũ_s = I, k_0 ≤ 2k, 1 ≤ M; reason: Algorithm 3's input conventions; a block size is positive
--   - reading: Algorithms 1 and 3 use δ (lines 5, 7) without listing it as an input → δ is an explicit input; Algorithm 3 passes δ/2^ℓ to each Algorithm 1 call and Algorithm 4 passes δ/n to each layer; reason: these are the union bounds of the proofs of Lemmas 3.7 (p. 11) and 4.3 (p. 17)
--   - encoding: eigenvectors of a degenerate or zero matrix chosen arbitrarily (p. 15) → the statement holds for every SpectralChooser (any exact eigensolver returning a sorted orthonormal eigenbasis of each Hermitian input); reason: quantifying over all choosers is the source's 'arbitrary' choice
--   - encoding: prefix s ∈ {0,1}^ℓ on the first ℓ qubits, Ũ_s of size 2^{n−ℓ} × k_0 → separate prefix and suffix lengths ℓ and m with ℓ + m = n; Ũ_s : 2^m × k_0; reason: m = n − ℓ without natural-number subtraction
--   - encoding: with probability at least 1 − δ → 1 − δ ≤ probability under the protocol's outcome law, for every δ > 0; reason: vacuous for δ ≥ 1, as in the source
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 11, Lemma 3.7 (proof pp. 11–12); Algorithm 3, p. 10

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
import Definitions.Def_QuantumOnePCA369_PauliPCA_SubspaceTomography

namespace QuantumOnePCA369.PauliPCA

theorem subspace_tomography_error :
    ∃ (K : ℕ) (C : ℝ), 0 < C ∧
      ∀ (ch : SpectralChooser) (n ℓ m k₀ k M : ℕ) (p δ : ℝ)
        (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ) (ρ : Matrix (Bits n) (Bits n) ℂ),
        ℓ + m = n → 0 < p → p ≤ 1 / 2 → K ≤ k → k₀ ≤ 2 * k → 1 ≤ M →
        (∀ s, IsIsometry (U s)) → IsDensity ρ →
        ((alg3Protocol ch n ℓ m k₀ k M p δ U).copies : ℝ) ≤
            C * 2 ^ n * (n + 1) * M * Real.log (1 / p) ∧
          (∀ (rnd : Fin (alg3R ℓ k M p) → SymF2 m × Bits m)
              (out : Fin (alg3R ℓ k M p) × Bits m × Bits ℓ → Bits n) (s : Bits ℓ),
            ((alg3Protocol ch n ℓ m k₀ k M p δ U).output rnd out s).IsHermitian) ∧
          (0 < δ →
            1 - δ ≤ (alg3Protocol ch n ℓ m k₀ k M p δ U).prob ρ
              (fun (rnd : Fin (alg3R ℓ k M p) → SymF2 m × Bits m)
                  (out : Fin (alg3R ℓ k M p) × Bits m × Bits ℓ → Bits n) =>
                ∑ s ∈ Finset.univ.filter (fun s : Bits ℓ => p ≤ prefixMass ℓ m ρ s),
                    opNorm ((alg3Protocol ch n ℓ m k₀ k M p δ U).output rnd out s -
                        (U s).conjTranspose * prefixBlock ℓ m ρ s * U s) ^ 2 /
                      prefixMass ℓ m ρ s ≤
                  C * k * (ℓ + 1) * Real.log (k / (p * δ)) / M)) := by sorry

end QuantumOnePCA369.PauliPCA
