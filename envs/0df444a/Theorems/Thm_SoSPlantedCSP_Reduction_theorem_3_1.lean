-- Prove2me | Theorems.Thm_SoSPlantedCSP_Reduction_theorem_3_1
-- name    : SoSPlantedCSP.Reduction.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:54.670286+00:00
-- url     : https://prove2.me/theorems/25ba073c-b0ba-4a56-886c-cd47997bc9fd
-- title:
--   Theorem 3.1 — SoS refutation of semirandom k-XOR yields exact de-noising of semirandom planted noisy k-XOR
-- statement:
--   Let $\mathcal H$ be a multiset of $m\ge1$ subsets of $[n]$, each of size $k$, let $\ell\ge1$ with $k/2\le\ell\le n/8$ (the runtime parameter), $\hat\varepsilon\in(0,1)$ (the bias guess) and $\gamma>0$. For $x^*\in\{-1,1\}^n$ and $\varepsilon$, $\mathrm{XOR}(\mathcal H,x^*,\varepsilon)$ draws $r_C\sim\mathrm{Bias}(\varepsilon)$ independently and sets $b_C=r_Cx^*_C$; $\mathrm{SoS}_{2\ell}$ is the set of degree-$2\ell$ pseudo-expectations over $\{-1,1\}^n$ and $\Phi(x)$ is the instance polynomial.
--
--   There are a randomized real-RAM program $\mathcal A$ and universal constants $C_t,c_t,C_f,c_f>0$ such that for all such $k,n,m,\ell,\mathcal H,\hat\varepsilon,\gamma$:
--
--   1. **Running time.** On input $(\ell,\hat\varepsilon,\gamma,\Psi)$ for any instance $\Psi=(\mathcal H,b)$, $\mathcal A$ halts within $C_t(n+m)^{c_t\ell}$ steps on every tape, and outputs a partition $\mathcal H_+\sqcup\mathcal H_-\sqcup\mathcal H_0=\mathcal H$.
--   2. **Guarantee.** Suppose degree-$2\ell$ sum-of-squares refutes $\mathrm{XOR}(\mathcal H,1^n,0)$: with probability at least $1-1/(mn)$ over $\Phi\sim\mathrm{XOR}(\mathcal H,1^n,0)$,
--   $$\max_{\tilde{\mathbb E}\in\mathrm{SoS}_{2\ell}}\tilde{\mathbb E}[\Phi(x)]\le\frac12+\frac{\gamma\hat\varepsilon}{720\log(mn)}.$$
--   Then for every $\varepsilon\in(0,1)$ and $x^*\in\{-1,1\}^n$, with probability at least $1-m|\hat\varepsilon-\varepsilon|-C_fn^{-c_f}$ over $\Psi\sim\mathrm{XOR}(\mathcal H,x^*,\varepsilon)$ and the tape:
--      (1) $b_C=x^*_C$ for every $C\in\mathcal H_+$; (2) $b_C=-x^*_C$ for every $C\in\mathcal H_-$; (3) $|\mathcal H_0|\le\gamma|\mathcal H|$.
--
--   This is the paper's main result, the formal version of its Theorem 1: an SoS refutation certificate for random right-hand sides on a worst-case hypergraph yields an algorithm that de-noises a planted instance on the same hypergraph, correctly classifying every constraint it does not discard, in time comparable to the refutation. Combined with known semirandom k-XOR refutation results it gives semirandom planted k-XOR and k-CSP algorithms with a runtime versus number of constraints trade-off.
--
--   **Formalization Note** The paper writes $(n+m)^{O(\ell)}$ and $1/\mathrm{poly}(n)$; the Lean statement quantifies universal constants $C_t,c_t,C_f,c_f$, chosen before every instance parameter, and the step budget $\lfloor C_t(n+m)^{c_t\ell}\rfloor$ is independent of $\hat\varepsilon$ and $\gamma$. The explicit numbers $720$, $1-1/(mn)$, $m|\hat\varepsilon-\varepsilon|$ and $\gamma|\mathcal H|$ are as printed. $\log$ is the natural logarithm. The guarantee is stated as "the failure probability is at most $m|\hat\varepsilon-\varepsilon|+C_fn^{-c_f}$", with outer tape measures.
--
--   Differences from the source:
--   - generalization: "Let k, n ∈ ℕ. There is an algorithm 𝒜" (one algorithm per k, n) → one program for all k, n, m, ℓ, ε̂, γ, with universal constants chosen first; reason: a uniform algorithm with uniform constants specializes to an algorithm for each fixed k, n
--   - reading: γ occurs in the hypothesis and clause (3) but is not listed among the inputs → γ > 0 is an input of 𝒜, and the running-time bound does not depend on it; reason: the algorithm runs Prune (Algorithm 3.8), which needs γ; for γ ≤ 0 clause (3) forces ℋ₀ = ∅ and the hypothesis fails once mn ≥ 8, so nothing is lost
--   - reading: log of unspecified base → natural logarithm; reason: the only log is in the hypothesis, where a smaller log weakens the hypothesis, so the natural log gives the stronger theorem; the proof's constants are calibrated to it
--   - encoding: Φ ∼ XOR(ℋ, 0) → Φ ∼ XOR(ℋ, 1ⁿ, 0); reason: at bias 0 every planted vector gives the uniform law, and Lemma 3.5, Theorem 1 and Corollary 3.2 write XOR(ℋ, 1ⁿ, 0)
--   - encoding: k/2 ≤ ℓ ≤ n/8, degree-2ℓ pseudo-expectations, m hyperedges, 1/mn → k ≤ 2ℓ, 8ℓ ≤ n, ℓ ≥ 1, m ≥ 1; reason: SoS_{2ℓ} is defined for 2ℓ ≥ 2 (Definition 2.2) and 1/mn needs m ≥ 1; nothing defined is excluded
--   - encoding: time (n+m)^{O(ℓ)} and probability 1 − m|ε̂ − ε| − 1/poly(n) → a halting bound ⌊C_t (n+m)^{c_t ℓ}⌋ steps on every input and every tape, and failure probability ≤ m|ε̂ − ε| + C_f n^{−c_f}, with universal C_t, c_t, C_f, c_f > 0; reason: the paper names no machine model and leaves the O(·) and poly constants universal
--   - encoding: with probability ≥ 1 − x over Ψ (and the algorithm's coins) → failure probability ≤ x over Ψ and the tape, tape probabilities as outer measures; reason: complementary events; outer measures only make the bound harder
--   - encoding: max over SoS_{2ℓ} ≤ c → every Ẽ ∈ SoS_{2ℓ} has Ẽ[Φ] ≤ c; reason: equivalent, and avoids proving attainment
--   - encoding: multiset ℋ and partition ℋ₊ ⊔ ℋ₋ ⊔ ℋ₀ = ℋ → H : Fin m → Finset (Fin n) with |H j| = k, the partition of positions given by the sign of output cell −(j+1); reason: repeated hyperedges are kept apart by position and |ℋ₀| counts multiplicity; the total decoding makes every output a partition
-- source:
--   Arpon Basu, Andrew D. Lin, Peter Manohar, STOC 2027 submission #544 (October 2026), Theorem 3.1, p. 10 (PDF p. 12); proof pp. 11–12 (PDF pp. 13–14); informal version Theorem 1, p. 3 (PDF p. 5)

import Mathlib
import Definitions.Def_SoSPlantedCSP_Reduction_Machine
import Definitions.Def_SoSPlantedCSP_Reduction_KXOR
import Definitions.Def_SoSPlantedCSP_Reduction_SoS
import Definitions.Def_SoSPlantedCSP_Reduction_IO

namespace SoSPlantedCSP.Reduction

/-- Theorem 3.1, Basu–Lin–Manohar, STOC 2027 submission #544, printed p. 10 (PDF p. 12).
One randomized real-RAM program `𝒜` and constants `Cₜ, cₜ, C_f, c_f > 0` such that, for all
`k, n, m, ℓ` with `k/2 ≤ ℓ ≤ n/8`, `ℓ ≥ 1`, `m ≥ 1`, every `k`-uniform hypergraph `ℋ` with `m`
hyperedges, `ε̂ ∈ (0,1)` and `γ > 0`:
(runtime) on input `(ℓ, ε̂, γ, Ψ)` `𝒜` halts within `Cₜ (n+m)^{cₜ ℓ}` steps for every
right-hand side vector and every tape, its output being a partition `ℋ₊ ⊔ ℋ₋ ⊔ ℋ₀` of `ℋ`;
(guarantee) if, with probability `≥ 1 − 1/(mn)` over `Φ ∼ XOR(ℋ, 1ⁿ, 0)`, every degree-`2ℓ`
pseudo-expectation has `Ẽ[Φ] ≤ 1/2 + γ ε̂ / (720 log(mn))`, then for every `ε ∈ (0,1)` and
`x* ∈ {−1,1}^n`, the probability over `Ψ ∼ XOR(ℋ, x*, ε)` and the tape that the output fails
(1)–(3) is at most `m |ε̂ − ε| + C_f n^{−c_f}`. -/
theorem theorem_3_1 :
    ∃ A : Program, ∃ Ct ct Cf cf : ℝ, 0 < Ct ∧ 0 < ct ∧ 0 < Cf ∧ 0 < cf ∧
      ∀ (k n m ℓ : ℕ) (H : Fin m → Finset (Fin n)), (∀ j, (H j).card = k) →
      ∀ (εhat γ : ℝ), 1 ≤ ℓ → k ≤ 2 * ℓ → 8 * ℓ ≤ n → 1 ≤ m →
        0 < εhat → εhat < 1 → 0 < γ →
        (∀ (b : Fin m → ℤˣ) (ω : Tape),
          HaltsWithin A (encMain k ℓ εhat γ H b) ω ⌊Ct * ((n : ℝ) + m) ^ (ct * ℓ)⌋₊) ∧
        (RefutationHyp H ℓ (γ * εhat / (720 * Real.log ((m : ℝ) * n))) →
          ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ xstar : Fin n → ℤˣ,
            jointProb (xorMass H xstar ε)
                (fun b ω => ¬ MainSuccess H γ xstar b (finalMem A (encMain k ℓ εhat γ H b) ω)) ≤
              m * |εhat - ε| + Cf * (n : ℝ) ^ (-cf)) := by sorry

end SoSPlantedCSP.Reduction
