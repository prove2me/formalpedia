-- Prove2me | Theorems.Thm_SoSPlantedCSP_Reduction_lemma_3_5
-- name    : SoSPlantedCSP.Reduction.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:56.429194+00:00
-- url     : https://prove2.me/theorems/9cba4572-e9ec-499a-95a4-d28f463fe643
-- title:
--   Lemma 3.5 — noise prediction and pruning (corrected: Prune time $(n+m)^{O(\ell)}$)
-- statement:
--   Let $\mathcal H$ be a multiset of $m\ge1$ subsets of $[n]$, each of size $k$, let $\ell\ge1$ with $k/2\le\ell\le n/8$, let $\hat\varepsilon\in(0,1)$ (the bias guess) and $\gamma>0$. For $y\in\{-1,1\}^n$ and $\varepsilon\in[0,1]$, $\mathrm{XOR}(\mathcal H,y,\varepsilon)$ is the semirandom planted noisy k-XOR law, and $\mathrm{SoS}_{2\ell}$ is the set of degree-$2\ell$ pseudo-expectations over $\{-1,1\}^n$.
--
--   There are randomized real-RAM programs Predict and Prune and universal constants $C_t,c_t>0$ such that for all such $k,n,m,\ell,\mathcal H,\hat\varepsilon,\gamma$:
--
--   1. **Predict.** On input $(\ell,\hat\varepsilon,\Psi)$ for any instance $\Psi=(\mathcal H,b)$, Predict halts within $C_t(n+m)^{c_t\ell}$ steps on every tape and outputs a function $\mathrm{pred}(\Psi,\cdot):\mathcal H\to\{-1,1\}$.
--   2. **Prune.** On input $(\ell,\hat\varepsilon,\gamma,\mathcal H)$, Prune halts within $C_t(n+m)^{c_t\ell}$ steps on every tape and outputs $\mathcal H'\subseteq\mathcal H$ with $|\mathcal H'|\ge(1-\gamma)m$.
--   3. **Guarantee.** Suppose that with probability at least $1-1/(mn)$ over $\Phi\sim\mathrm{XOR}(\mathcal H,1^n,0)$,
--   $$\max_{\tilde{\mathbb E}\in\mathrm{SoS}_{2\ell}}\tilde{\mathbb E}[\Phi(x)]\le\frac12+\frac{\hat\varepsilon\gamma}{18}.$$
--   Then for every $\varepsilon\in[0,1]$, with probability at least $1-1/n-m|\hat\varepsilon-\varepsilon|$ over Prune's tape, for every $C\in\mathcal H'$ and every $y\in\{-1,1\}^n$,
--   $$\Pr_{\Psi\sim\mathrm{XOR}(\mathcal H,y,\varepsilon)}\big[\mathrm{pred}(\Psi,C)=y_C\big]\ge\frac23-m|\hat\varepsilon-\varepsilon|,$$
--   the inner probability being over $\Psi$ and Predict's own tape.
--
--   Predict is the noise predictor: it guesses, constraint by constraint, whether the right-hand side agrees with the planted assignment. Prune finds, without seeing any right-hand sides, a large set of constraints on which the predictor is reliable against every planted assignment. Lemma 3.5 is the second and third step of the proof of Theorem 3.1.
--
--   **Formalization Note** The paper writes $(n+m)^{O(\ell)}$ and $n^{O(\ell)}$; the Lean statement quantifies universal constants $C_t,c_t$, chosen before every instance parameter and independent of $\hat\varepsilon$ and $\gamma$, and the step budget is $\lfloor C_t(n+m)^{c_t\ell}\rfloor$. Probabilities are stated as failure bounds: "$\ge 2/3-x$" as "$\Pr[\mathrm{pred}\ne y_C]\le1/3+x$" and "with probability $1-1/n-x$" as "the failure probability over Prune's tape is at most $1/n+x$", with outer tape measures. The multiset is an indexed family of positions; predictions and membership in $\mathcal H'$ are per position.
--
--   Differences from the source:
--   - correction: Prune runs in time n^{O(ℓ)} → Prune runs in time (n+m)^{O(ℓ)}; reason: the printed bound is false when m is not polynomially bounded in n; counterexample with k = 2, n = 8, ℓ = 1, ε̂ = ε = 1/10, γ = 1/2: let I₀ have M copies of each of the 15 pairs inside {1,…,6} plus one copy of {1,2}, and let I_π replace position π by {7,8}; for large M both satisfy the hypothesis, b at {7,8} is the only information on y₇y₈ in I_π, so every predictor errs there with probability ≥ 0.45 for some y and the guarantee forces π ∉ ℋ′ with probability ≥ 7/8; a run reading at most R cells cannot tell I_π from I₀ unless it reads position π, so 7m/8 ≤ R + m/2, impossible for a bound R independent of m
--   - generalization: "Let k, n ∈ ℕ. There is an algorithm" (one algorithm per k, n) → one Predict and one Prune for all k, n, m, ℓ, ε̂, γ, with universal constants chosen first; reason: a uniform algorithm with uniform constants specializes to an algorithm for each fixed k, n
--   - generalization: Prune, its running time and its size bound |ℋ′| ≥ (1 − γ)m are asserted under the refutation hypothesis ("Suppose further … Then there is … Prune") → Prune's running time and size bound hold on every input (ℓ, ε̂, γ, ℋ) and every tape, whether or not the refutation hypothesis holds; only clause (c) is conditional; reason: a Prune with these properties is in particular one for every ℋ satisfying the hypothesis, so the Lean statement specializes to the printed one
--   - reading: Predict is called deterministic, with probability over Ψ only → Predict is a program with its own random tape, and the inner probability is over Ψ and that tape; reason: Algorithm 3.7 (the paper's Predict) samples uniform bits r₁, …, rₙ in step (1) and the proof uses that pred randomizes the plant; the literal reading contradicts the paper's own algorithm
--   - reading: Prune "takes in ℋ", γ unspecified → Prune takes (ℓ, ε̂, γ, ℋ), never b, y or ε, and γ > 0; reason: Algorithm 3.8 runs Predict with bias guess ε̂ for max(1300γ⁻¹ log n, 288 log(mn)) rounds, so it needs ℓ, ε̂ and γ; γ is the fraction of discarded constraints
--   - reading: "outputs some ℋ′ ⊆ ℋ of size at least (1 − γ)m such that with probability …" → the size bound holds on every run, outside the probability event; reason: literal reading of the sentence
--   - reading: ε unquantified → every ε ∈ [0,1]; reason: Bias(ε) is a law exactly for these ε (Definition 2.1 requires ε ≥ 0)
--   - encoding: k/2 ≤ ℓ ≤ n/8, degree-2ℓ pseudo-expectations, m hyperedges, 1/mn → k ≤ 2ℓ, 8ℓ ≤ n, ℓ ≥ 1, m ≥ 1; reason: SoS_{2ℓ} is defined for 2ℓ ≥ 2 (Definition 2.2) and 1/mn needs m ≥ 1; nothing defined is excluded
--   - encoding: (n+m)^{O(ℓ)} time → a halting bound ⌊C_t (n+m)^{c_t ℓ}⌋ steps on every input and every tape, universal C_t, c_t > 0 independent of ε̂ and γ; reason: the paper names no machine model and leaves the O(·) constant universal
--   - encoding: probabilities ≥ 2/3 − m|ε̂ − ε| and ≥ 1 − 1/n − m|ε̂ − ε| → failure probabilities ≤ 1/3 + m|ε̂ − ε| and ≤ 1/n + m|ε̂ − ε|, tape probabilities as outer measures; reason: complementary events; outer measures only make the bounds harder
--   - encoding: max over SoS_{2ℓ} ≤ c → every Ẽ ∈ SoS_{2ℓ} has Ẽ[Φ] ≤ c; reason: equivalent, and avoids proving attainment
--   - encoding: multiset ℋ, pred : ℋ → {−1,1}, ℋ′ ⊆ ℋ → H : Fin m → Finset (Fin n) with |H j| = k, predictions and ℋ′ per position, read from output cells −(j+1) with total decoding; reason: repeated hyperedges are kept apart by position; a total decoding changes no instance
-- source:
--   Arpon Basu, Andrew D. Lin, Peter Manohar, STOC 2027 submission #544 (October 2026), Lemma 3.5 (Noise prediction algorithm), p. 11 (PDF p. 13); restated with proof, Algorithms 3.7 and 3.8, pp. 12–14 (PDF pp. 14–16)

import Mathlib
import Definitions.Def_SoSPlantedCSP_Reduction_Machine
import Definitions.Def_SoSPlantedCSP_Reduction_KXOR
import Definitions.Def_SoSPlantedCSP_Reduction_SoS
import Definitions.Def_SoSPlantedCSP_Reduction_IO

namespace SoSPlantedCSP.Reduction

/-- Lemma 3.5 (noise prediction algorithm), Basu–Lin–Manohar, STOC 2027 submission #544,
printed p. 11 (PDF p. 13), restated p. 12 (PDF p. 14), with Prune's running time corrected from
`n^{O(ℓ)}` to `(n+m)^{O(ℓ)}`. Two randomized real-RAM programs `Predict` and `Prune` and
constants `Cₜ, cₜ > 0` such that, for all `k, n, m, ℓ` with `k/2 ≤ ℓ ≤ n/8`, `ℓ ≥ 1`, `m ≥ 1`,
every `k`-uniform hypergraph `ℋ` with `m` hyperedges, `ε̂ ∈ (0,1)` and `γ > 0`:
(a) `Predict` on `(ℓ, ε̂, Ψ)` halts within `Cₜ (n+m)^{cₜ ℓ}` steps for every instance and tape;
(b) `Prune` on `(ℓ, ε̂, γ, ℋ)` halts within `Cₜ (n+m)^{cₜ ℓ}` steps on every tape, with an
output `ℋ′` of size at least `(1 − γ) m`;
(c) if degree-`2ℓ` SoS refutes `XOR(ℋ, 1ⁿ, 0)` at threshold `1/2 + ε̂γ/18` with probability
`≥ 1 − 1/(mn)`, then for every `ε ∈ [0,1]`, with probability at least `1 − 1/n − m|ε̂ − ε|` over
`Prune`'s tape, for every `C ∈ ℋ′` and every `y`,
`Pr_{Ψ ∼ XOR(ℋ, y, ε), Predict's tape}[pred(Ψ, C) ≠ y_C] ≤ 1/3 + m|ε̂ − ε|`. -/
theorem lemma_3_5 :
    ∃ Predict Prune : Program, ∃ Ct ct : ℝ, 0 < Ct ∧ 0 < ct ∧
      ∀ (k n m ℓ : ℕ) (H : Fin m → Finset (Fin n)), (∀ j, (H j).card = k) →
      ∀ (εhat γ : ℝ), 1 ≤ ℓ → k ≤ 2 * ℓ → 8 * ℓ ≤ n → 1 ≤ m →
        0 < εhat → εhat < 1 → 0 < γ →
        (∀ (b : Fin m → ℤˣ) (ω : Tape),
          HaltsWithin Predict (encPredict k ℓ εhat H b) ω
            ⌊Ct * ((n : ℝ) + m) ^ (ct * ℓ)⌋₊) ∧
        (∀ ω : Tape,
          HaltsWithin Prune (encPrune k ℓ εhat γ H) ω ⌊Ct * ((n : ℝ) + m) ^ (ct * ℓ)⌋₊ ∧
          (1 - γ) * m ≤
            ((pruneOut (m := m) (finalMem Prune (encPrune k ℓ εhat γ H) ω)).card : ℝ)) ∧
        (RefutationHyp H ℓ (εhat * γ / 18) →
          ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
            (tapeLaw {ω | ¬ ∀ j ∈ pruneOut (m := m) (finalMem Prune (encPrune k ℓ εhat γ H) ω),
                ∀ y : Fin n → ℤˣ,
                  jointProb (xorMass H y ε)
                      (fun b ω' => predOut (finalMem Predict (encPredict k ℓ εhat H b) ω') j ≠
                        monoSign y (H j)) ≤
                    1 / 3 + m * |εhat - ε|}).toReal ≤
              1 / n + m * |εhat - ε|) := by sorry

end SoSPlantedCSP.Reduction
