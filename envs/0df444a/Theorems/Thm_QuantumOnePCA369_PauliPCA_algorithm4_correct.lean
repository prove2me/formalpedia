-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_algorithm4_correct
-- name    : QuantumOnePCA369.PauliPCA.algorithm4_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:01.360393+00:00
-- url     : https://prove2.me/theorems/ab844f3a-7371-42d6-981f-9a19b10a77e3
-- title:
--   Lemma 4.3 — Algorithm 4 recovers the top eigenvector with $\tilde O(2^n\eta^2/(\Delta^3\varepsilon^3)\log(1/\delta))$ copies (corrected: $\log(1/\delta)$ near $\delta=1$)
-- statement:
--   Let $\Delta,\eta>0$ and let $\rho$ be an $n$-qubit state ($n\ge1$) with unit top eigenvector $|\psi\rangle$, top eigenvalue $\lambda\ge1-\eta$ of multiplicity one, and spectral gap at least $\Delta$. Let $\varepsilon,\delta>0$ with $\varepsilon\le\eta$. There are universal constants $C_M$ (the constant of Algorithm 4, line 3), $C$ and $a$ such that Algorithm 4, given $\Delta,\eta,\varepsilon,\delta$ and run with any exact eigensolver, uses
--   $$N\le\Big\lceil C\,\frac{2^n\eta^2}{\Delta^3\varepsilon^3}\,L^a\,D\Big\rceil$$
--   copies of $\rho$, $L=n+\log(2+1/\varepsilon)+\log(2+1/\Delta)+\log(2+\eta)$, $D=\log(2+1/\delta)$, and on every run produces a unit vector (a pure state) $|\hat\psi\rangle$, which satisfies
--   $$|\langle\hat\psi|\psi\rangle|^2\ge1-\varepsilon$$
--   with probability at least $1-\delta$.
--
--   This is the accuracy and copy-complexity half of Theorem 1.1, in the generality of arbitrary bounds $\eta,\Delta$ on the noise level and the gap.
--
--   **Formalization Note** The spectral hypotheses are written as $\rho|\psi\rangle=\lambda|\psi\rangle$, $\lambda\ge1-\eta$, and $\langle w|\rho|w\rangle\le(\lambda-\Delta)\|w\|_2^2$ for every $w\perp\psi$, which says that every other eigenvalue is at most $\lambda-\Delta$. Algorithm 4 uses $k=\lceil n\eta/(\Delta\varepsilon)\rceil$ and $p=\varepsilon\Delta/n$ exactly as printed; only $M$ carries the free constant.
--
--   Differences from the source:
--   - correction: factor log(1/δ) in the Õ-bound, for all δ > 0 → factor D = log(2 + 1/δ); reason: log(1/δ) → 0 as δ → 1 forces N = 0 for δ close to 1, which is false: for n = 2 and a pure state (λ = Δ = 1, η = ε < 1) an algorithm with no copies succeeds with probability at most ε^3 for some state, while 1 − δ = τ can be chosen larger than ε^3; D ≤ 2 log(1/δ) for δ ≤ 1/2, so nothing changes in the range the paper means
--   - encoding: Õ(·), suppressing polylogarithmic factors in 1/ε, 1/Δ, η, 2^n → ≤ ⌈C · 2^n η^2/(Δ^3 ε^3) · L^a · D⌉ with L = n + log(2+1/ε) + log(2+1/Δ) + log(2+η) and universal C, a quantified before every instance; reason: a power of L dominates every polylogarithm in those quantities; the ceiling absorbs integer rounding
--   - encoding: Algorithm 4 with block size M = O(n^5η^2/(Δ^3ε^3) · log(n^3η/(Δ^2ε^2δ))) (line 3) → M = ⌈C_M · n^5η^2/(Δ^3ε^3) · log(n^3η/(Δ^2ε^2δ))⌉ with the constant C_M existentially quantified before every instance; k = ⌈nη/(Δε)⌉ and p = εΔ/n exactly as printed; reason: the O(·) in line 3 is the algorithm's universal constant
--   - encoding: top eigenvector |ψ⟩, top eigenvalue (of multiplicity one) at least 1 − η, spectral gap at least Δ → unit ψ with ρψ = λψ, 1 − η ≤ λ, and ⟨w|ρ|w⟩ ≤ (λ − Δ)‖w‖² for all w ⊥ ψ; reason: equivalent by the spectral theorem: the second eigenvalue is the maximum Rayleigh quotient on ψ^⊥
--   - encoding: an n-qubit state → 1 ≤ n; reason: Algorithm 4 (lines 5 and 13) needs a first qubit
--   - encoding: ε, δ > 0 arbitrary → if ε ≥ 1 or δ ≥ 1 the algorithm measures no copy and returns the basis vector |0…0⟩ after a constant number of charged steps; reason: for ε ≥ 1 every unit vector satisfies the fidelity requirement and for δ ≥ 1 the requirement is vacuous; no positive ε or δ is excluded
--   - reading: Algorithms 1 and 3 use δ (lines 5, 7) without listing it as an input → δ is an explicit input; Algorithm 3 passes δ/2^ℓ to each Algorithm 1 call and Algorithm 4 passes δ/n to each layer; reason: these are the union bounds of the proofs of Lemmas 3.7 (p. 11) and 4.3 (p. 17)
--   - reading: line 14 gives no mass threshold for layer 0 → threshold p_0 = p (= p/2^0); reason: the proof's sum over ℓ = 0 on p. 17 uses p/2^ℓ at ℓ = 0
--   - encoding: measure the last n − ℓ qubits in the σ_{x,A_r x+c_r} basis and observe O ∈ {±1} → each qubit with label (x_j, z_j) = (1,0), (1,1), (0,1) is measured in X, Y, Z; at (0,0) it is measured in Z and its bit ignored; O is the product of (−1)^{y_j} over the non-identity sites; reason: this is the Pauli basis measurement of σ_{x,z} = ⊗_j i^{x_j z_j} X^{x_j} Z^{z_j} (p. 6)
--   - encoding: eigenvectors of a degenerate or zero matrix chosen arbitrarily (p. 15) → the statement holds for every SpectralChooser (any exact eigensolver returning a sorted orthonormal eigenbasis of each Hermitian input); reason: quantifying over all choosers is the source's 'arbitrary' choice
--   - encoding: the algorithm is given N copies and performs non-adaptive Pauli basis measurements → the algorithm is a PauliProtocol: uniformly random internal randomness, one product Pauli setting per copy depending only on the randomness, independent Born-rule outcomes, and a costed classical decoder; probabilities are finite sums over randomness and outcomes; reason: non-adaptivity and the Pauli restriction hold by the type; the state enters only through the outcome law
--   - encoding: produces a pure state |ψ̂⟩ → the output is a classical description (a basis vector or a dense array of 2^n complex amplitudes) of a vector of C^{2^n}; reason: a classical description is what the algorithm returns; the described vector has unit norm on every run, stated as its own clause
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 15, Lemma 4.3 (proof pp. 15–18); Algorithm 4, p. 15

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
import Definitions.Def_QuantumOnePCA369_PauliPCA_SubspacePruning

namespace QuantumOnePCA369.PauliPCA

theorem algorithm4_correct :
    ∃ CM C a : ℝ, ∀ (ch : SpectralChooser) (n : ℕ) (ρ : Matrix (Bits n) (Bits n) ℂ)
      (ψ : Bits n → ℂ) (lam Δ η ε δ : ℝ),
      1 ≤ n → IsDensity ρ → normSq2 ψ = 1 → ρ.mulVec ψ = (lam : ℂ) • ψ → 1 - η ≤ lam →
      (∀ w : Bits n → ℂ, braket ψ w = 0 →
        (braket w (ρ.mulVec w)).re ≤ (lam - Δ) * normSq2 w) →
      0 < Δ → 0 < η → 0 < ε → ε ≤ η → 0 < δ →
      (alg4 ch CM n Δ η ε δ).copies ≤
          ⌈C * 2 ^ n * η ^ 2 / (Δ ^ 3 * ε ^ 3) * polylogL n Δ η ε ^ a * confD δ⌉₊ ∧
        (∀ (r : (alg4 ch CM n Δ η ε δ).Rand) (y : (alg4 ch CM n Δ η ε δ).Copy → Bits n),
          normSq2 ((alg4 ch CM n Δ η ε δ).output r y).toVec = 1) ∧
        1 - δ ≤ (alg4 ch CM n Δ η ε δ).prob ρ
          (fun r y => 1 - ε ≤ Complex.normSq (braket ((alg4 ch CM n Δ η ε δ).output r y).toVec ψ)) := by sorry

end QuantumOnePCA369.PauliPCA
