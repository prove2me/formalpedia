-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_subspace_tomography_time
-- name    : QuantumOnePCA369.PauliPCA.subspace_tomography_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:37.991735+00:00
-- url     : https://prove2.me/theorems/6b406a92-283c-48d1-8e59-55b5aa5fc1ed
-- title:
--   Lemma 3.8 — Algorithm 3 runs in $O(2^nn^2M\,\mathrm{poly}(k)\log(1/p_\ell)^2)$ time (corrected: $n$ to $n+1$)
-- statement:
--   Let $n=\ell+m$, $p_\ell\in(0,1/2]$, $k\ge1$, $k_0\le2k$ and $M\ge1$. There are universal constants $C,a$ such that for all $2^m\times k_0$ matrices $\tilde U_s$, every confidence $\delta$, every exact eigensolver and every run (randomness and outcomes), Algorithm 3 runs in time at most
--   $$C\,2^n(n+1)^2M\,k^{a}\log(1/p_\ell)^2,$$
--   counting $n$ ticks per measured copy.
--
--   This is the per-layer running time that Lemma 4.4 sums over the layers of Algorithm 4.
--
--   Running time is the tick count of the program in the unit-cost real RAM of §2 (p. 5): one tick per real or complex arithmetic operation, square root, logarithm, ceiling, comparison, array read or write and loop step, $n$ ticks per measured copy, and one call of an exact eigensolver on a $d'\times d'$ Hermitian matrix charged $d'^3+1$. The cubic charge is a chosen polynomial envelope for this idealized primitive, not a bit-complexity or numerical-stability claim.
--
--   Differences from the source:
--   - correction: O(2^n n² M poly(k) log(1/p_ℓ)²) → ≤ C · 2^n (n+1)² M k^a log(1/p_ℓ)²; reason: at n = 0 (ℓ = m = 0) the program executes charged steps (at least one Algorithm 1 call) while the printed bound is 0; for n ≥ 1 the bounds agree up to a factor 4
--   - encoding: poly(k) → k^a with universal a, k ≥ 1; reason: a polynomial in k ≥ 1 is dominated by a power of k
--   - encoding: Algorithm 3's inputs: partial unitaries with k_0 ≤ 2k, block size M → 1 ≤ k, k_0 ≤ 2k, 1 ≤ M; reason: a dimension and a block size are positive
--   - generalization: partial unitaries Ũ_s → arbitrary complex 2^m × k_0 matrices, every δ, every run; reason: the running-time bound does not use the entries; the source's case is a special case
--   - encoding: running time in the real RAM model with spectral computations' numerical details omitted (p. 5) → tick count of the defined program: one tick per scalar operation, comparison, array access and loop step, n ticks per measured copy, an exact eigensolver charged d'^3 + 1; reason: §2 defers spectral computations to the real RAM model; the cubic charge is a polynomial envelope and the paper's bounds only use poly(d')
--   - reading: Algorithms 1 and 3 use δ (lines 5, 7) without listing it as an input → δ is an explicit input; Algorithm 3 passes δ/2^ℓ to each Algorithm 1 call and Algorithm 4 passes δ/n to each layer; reason: these are the union bounds of the proofs of Lemmas 3.7 (p. 11) and 4.3 (p. 17)
--   - encoding: eigenvectors of a degenerate or zero matrix chosen arbitrarily (p. 15) → the statement holds for every SpectralChooser (any exact eigensolver returning a sorted orthonormal eigenbasis of each Hermitian input); reason: quantifying over all choosers is the source's 'arbitrary' choice
--   - encoding: prefix s ∈ {0,1}^ℓ on the first ℓ qubits, Ũ_s of size 2^{n−ℓ} × k_0 → separate prefix and suffix lengths ℓ and m with ℓ + m = n; Ũ_s : 2^m × k_0; reason: m = n − ℓ without natural-number subtraction
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 12, Lemma 3.8; Algorithm 3, p. 10

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
import Definitions.Def_QuantumOnePCA369_PauliPCA_SubspaceTomography

namespace QuantumOnePCA369.PauliPCA

theorem subspace_tomography_time :
    ∃ C a : ℝ, ∀ (ch : SpectralChooser) (n ℓ m k₀ k M : ℕ) (p δ : ℝ)
      (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ),
      ℓ + m = n → 0 < p → p ≤ 1 / 2 → 1 ≤ k → k₀ ≤ 2 * k → 1 ≤ M →
      ∀ (rnd : Fin (alg3R ℓ k M p) → SymF2 m × Bits m)
        (out : Fin (alg3R ℓ k M p) × Bits m × Bits ℓ → Bits n),
        ((alg3Protocol ch n ℓ m k₀ k M p δ U).runTime rnd out : ℝ) ≤
          C * 2 ^ n * (n + 1) ^ 2 * M * (k : ℝ) ^ a * Real.log (1 / p) ^ 2 := by sorry

end QuantumOnePCA369.PauliPCA
