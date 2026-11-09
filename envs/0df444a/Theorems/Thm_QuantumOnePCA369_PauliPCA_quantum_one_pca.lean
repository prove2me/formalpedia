-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_quantum_one_pca
-- name    : QuantumOnePCA369.PauliPCA.quantum_one_pca
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:30.919029+00:00
-- url     : https://prove2.me/theorems/082072ee-40b9-4863-b7ba-3e077be3a2f8
-- title:
--   Theorem 1.1 — quantum 1-PCA from non-adaptive Pauli measurements in nearly linear copies and time (corrected: $\log(1/\delta)$ near $\delta=1$)
-- statement:
--   Let $\rho$ be an unknown $n$-qubit state ($n\ge1$) with top eigenvalue $\lambda$, second eigenvalue $\lambda_2<\lambda$ and unit top eigenvector $|\psi\rangle$; let $\Delta=\lambda-\lambda_2$, let $\varepsilon,\delta>0$ and $\eta=\max(1-\lambda,\varepsilon)$. There are universal constants $C_M,C,a$ such that Algorithm 4 (with constant $C_M$), given $\Delta,\eta,\varepsilon,\delta$ and run with any exact eigensolver:
--
--   1. uses only non-adaptive single-qubit Pauli basis measurements, on
--   $$N\le\Big\lceil C\,\frac{2^n}{\varepsilon}\cdot\frac{\eta^2}{\Delta^3\varepsilon^2}\,L^aD\Big\rceil$$
--   copies of $\rho$;
--   2. on every run, takes time at most
--   $$C\Big\lceil\frac{2^n}{\varepsilon}\Big(\frac{\eta}{\Delta\varepsilon}\Big)^{a}L^aD\Big\rceil$$
--   and outputs a description of a unit vector $|\hat\psi\rangle$ (a pure state);
--   3. with probability at least $1-\delta$, $|\langle\hat\psi|\psi\rangle|^2\ge1-\varepsilon$.
--
--   Here $L=n+\log(2+1/\varepsilon)+\log(2+1/\Delta)+\log(2+\eta)$ and $D=\log(2+1/\delta)$ stand for the polylogarithmic factors hidden by $\tilde O$ and for $\log(1/\delta)$.
--
--   This is the paper's main result: top-eigenvector recovery of a mixed state from single-copy, single-qubit, non-adaptively chosen Pauli measurements, with copy complexity and running time nearly linear in the dimension $2^n$ when $\Delta$ is constant and $\eta/\varepsilon=O(1)$, extending the pure-state result of [GGH+26] to mixed states.
--
--   Running time is the tick count of the program in the unit-cost real RAM of §2 (p. 5): one tick per real or complex arithmetic operation, square root, logarithm, ceiling, comparison, array read or write and loop step, $n$ ticks per measured copy, and one call of an exact eigensolver on a $d'\times d'$ Hermitian matrix charged $d'^3+1$. The cubic charge is a chosen polynomial envelope for this idealized primitive, not a bit-complexity or numerical-stability claim.
--
--   **Formalization Note** $\lambda,\lambda_2$ are the first two entries of the non-increasingly sorted spectrum. The algorithm is the defined protocol of Algorithm 4: the state is not an input, the measurement settings depend only on the internal randomness (non-adaptivity and the Pauli restriction hold by type), and the probability is the finite sum over randomness and Born-rule outcomes. $(\eta/(\Delta\varepsilon))^a=(1/\Delta)^a(\eta/\varepsilon)^a$ is a polynomial in $1/\Delta$ and $\eta/\varepsilon$.
--
--   Differences from the source:
--   - correction: factor log(1/δ) in the Õ-bound, for all δ > 0 → factor D = log(2 + 1/δ); reason: log(1/δ) → 0 as δ → 1 forces N = 0 for δ close to 1, which is false: for n = 2 and a pure state (λ = Δ = 1, η = ε < 1) an algorithm with no copies succeeds with probability at most ε^3 for some state, while 1 − δ = τ can be chosen larger than ε^3; D ≤ 2 log(1/δ) for δ ≤ 1/2, so nothing changes in the range the paper means
--   - encoding: Õ(·), suppressing polylogarithmic factors in 1/ε, 1/Δ, η, 2^n → ≤ ⌈C · 2^n η^2/(Δ^3 ε^3) · L^a · D⌉ with L = n + log(2+1/ε) + log(2+1/Δ) + log(2+η) and universal C, a quantified before every instance; reason: a power of L dominates every polylogarithm in those quantities; the ceiling absorbs integer rounding
--   - encoding: running time Õ((2^n/ε)·poly(1/Δ, η/ε)·log(1/δ)) → ≤ C·⌈(2^n/ε)·(η/(Δε))^a·L^a·D⌉ for every run; reason: (η/(Δε))^a = (1/Δ)^a (η/ε)^a is a polynomial in 1/Δ ≥ 1 and η/ε ≥ 1; powers of L absorb the logarithms
--   - encoding: top eigenvalue λ, second eigenvalue λ_2, top eigenvector |ψ⟩ → λ, λ_2 = first two entries of the sorted spectrum (eigenvalues₀); ψ a unit vector with ρψ = λψ; reason: the source's spectral data
--   - encoding: Algorithm 4 with block size M = O(n^5η^2/(Δ^3ε^3) · log(n^3η/(Δ^2ε^2δ))) (line 3) → M = ⌈C_M · n^5η^2/(Δ^3ε^3) · log(n^3η/(Δ^2ε^2δ))⌉ with the constant C_M existentially quantified before every instance; k = ⌈nη/(Δε)⌉ and p = εΔ/n exactly as printed; reason: the O(·) in line 3 is the algorithm's universal constant
--   - encoding: an n-qubit state → 1 ≤ n; reason: Algorithm 4 (lines 5 and 13) needs a first qubit
--   - encoding: ε, δ > 0 arbitrary → if ε ≥ 1 or δ ≥ 1 the algorithm measures no copy and returns the basis vector |0…0⟩ after a constant number of charged steps; reason: for ε ≥ 1 every unit vector satisfies the fidelity requirement and for δ ≥ 1 the requirement is vacuous; no positive ε or δ is excluded
--   - reading: Algorithms 1 and 3 use δ (lines 5, 7) without listing it as an input → δ is an explicit input; Algorithm 3 passes δ/2^ℓ to each Algorithm 1 call and Algorithm 4 passes δ/n to each layer; reason: these are the union bounds of the proofs of Lemmas 3.7 (p. 11) and 4.3 (p. 17)
--   - reading: line 14 gives no mass threshold for layer 0 → threshold p_0 = p (= p/2^0); reason: the proof's sum over ℓ = 0 on p. 17 uses p/2^ℓ at ℓ = 0
--   - encoding: measure the last n − ℓ qubits in the σ_{x,A_r x+c_r} basis and observe O ∈ {±1} → each qubit with label (x_j, z_j) = (1,0), (1,1), (0,1) is measured in X, Y, Z; at (0,0) it is measured in Z and its bit ignored; O is the product of (−1)^{y_j} over the non-identity sites; reason: this is the Pauli basis measurement of σ_{x,z} = ⊗_j i^{x_j z_j} X^{x_j} Z^{z_j} (p. 6)
--   - encoding: eigenvectors of a degenerate or zero matrix chosen arbitrarily (p. 15) → the statement holds for every SpectralChooser (any exact eigensolver returning a sorted orthonormal eigenbasis of each Hermitian input); reason: quantifying over all choosers is the source's 'arbitrary' choice
--   - encoding: the algorithm is given N copies and performs non-adaptive Pauli basis measurements → the algorithm is a PauliProtocol: uniformly random internal randomness, one product Pauli setting per copy depending only on the randomness, independent Born-rule outcomes, and a costed classical decoder; probabilities are finite sums over randomness and outcomes; reason: non-adaptivity and the Pauli restriction hold by the type; the state enters only through the outcome law
--   - encoding: produces a pure state |ψ̂⟩ → the output is a classical description (a basis vector or a dense array of 2^n complex amplitudes) of a vector of C^{2^n}; reason: a classical description is what the algorithm returns; the described vector has unit norm on every run, stated as its own clause
--   - encoding: the algorithm 'runs in time' → the run time (n ticks per copy plus the decoder's cost) is bounded on every run, for every eigensolver; reason: a worst-case bound over all outcomes and internal randomness
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 2, Theorem 1.1 (and the remark after it); proved by Lemmas 4.3 and 4.4, pp. 15–18; Algorithm 4, p. 15

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
import Definitions.Def_QuantumOnePCA369_PauliPCA_SubspacePruning

open scoped ComplexOrder

namespace QuantumOnePCA369.PauliPCA

theorem quantum_one_pca :
    ∃ CM C a : ℝ, ∀ (ch : SpectralChooser) (n : ℕ) (ρ : Matrix (Bits n) (Bits n) ℂ)
      (hρ : IsDensity ρ) (ψ : Bits n → ℂ) (ε δ : ℝ),
      let lam := sortedEig hρ.1.isHermitian 0
      let lam₂ := sortedEig hρ.1.isHermitian 1
      let Δ := lam - lam₂
      let η := max (1 - lam) ε
      let P := alg4 ch CM n Δ η ε δ
      1 ≤ n → lam₂ < lam → normSq2 ψ = 1 → ρ.mulVec ψ = (lam : ℂ) • ψ → 0 < ε → 0 < δ →
      P.copies ≤ ⌈C * 2 ^ n * η ^ 2 / (Δ ^ 3 * ε ^ 3) * polylogL n Δ η ε ^ a * confD δ⌉₊ ∧
        (∀ (r : P.Rand) (y : P.Copy → Bits n),
          (P.runTime r y : ℝ) ≤
              C * ⌈(2 : ℝ) ^ n / ε * (η / (Δ * ε)) ^ a * polylogL n Δ η ε ^ a * confD δ⌉₊ ∧
            normSq2 (P.output r y).toVec = 1) ∧
        1 - δ ≤ P.prob ρ (fun r y => 1 - ε ≤ Complex.normSq (braket (P.output r y).toVec ψ)) := by sorry

end QuantumOnePCA369.PauliPCA
