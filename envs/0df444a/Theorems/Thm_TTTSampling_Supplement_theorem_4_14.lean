-- Prove2me | Theorems.Thm_TTTSampling_Supplement_theorem_4_14
-- name    : TTTSampling.Supplement.theorem_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:01:31.386466+00:00
-- url     : https://prove2.me/theorems/42ac099b-9c4e-4db2-98a0-1c0b8a553c52
-- title:
--   Theorem 4.14 — KL lower bound $\Omega\big(\bar n^2\gamma^6/(K^2\log^2\bar n\,\log^2(2/\gamma))\big)$ queries for $D_{\mathrm{KL}}\le K$ at $R=(1+\gamma)^2$
-- statement:
--   Consider sampling from an arbitrary unknown distribution $\mu^\star$ on $\{0,1\}^{\bar n}$ (no class is known), with access to an oracle $\hat\mu:\{0,1\}^{\le \bar n}\to\mathbb R_{\ge0}$ satisfying **Assumption 3.1** with parameter $R$. Write $D_{\mathrm{KL}}(\hat\nu\,\|\,\mu^\star)$ for the Kullback–Leibler divergence in nats, equal to $+\infty$ unless $\hat\nu\ll\mu^\star$.
--
--   **Theorem.** There are a constant $c>0$ and a threshold $N_0$ such that for every $\bar n\ge N_0$, every $\gamma\in(1/\bar n,1)$ and every real $K\ge\gamma^2$, **no** randomized algorithm has the following guarantee: for every distribution $\mu^\star$ on $\{0,1\}^{\bar n}$ and every $\hat\mu$ satisfying Assumption 3.1 with $R=(1+\gamma)^2$, the algorithm makes at most
--
--   $$
--   c\cdot\frac{\bar n^2\gamma^6}{K^2\log^2(\bar n)\cdot\log^2(2/\gamma)}
--   $$
--
--   queries to $\hat\mu$ on every run and outputs a random string whose distribution $\hat\nu$ satisfies $D_{\mathrm{KL}}(\hat\nu\,\|\,\mu^\star)\le K$.
--
--   In words: an algorithm making strictly subquadratically many queries cannot achieve KL divergence sublinear in $\bar n$. This strengthens the conclusion of the main lower bound from total variation to KL divergence at the cost of the parameter dependence.
--
--   **Formalization Note** The algorithm is the base mission's `OracleProg`, chosen after $\bar n$, $\gamma$, $K$ and before $\mu^\star$, $\hat\mu$. $D_{\mathrm{KL}}$ is the definition `klDiv`. $\log$ in the budget is the natural logarithm.
--
--   Differences from the source:
--
--   - encoding: log of unspecified base in the query budget → natural logarithm; reason: a change of base multiplies the budget by a constant factor, absorbed by ∃ c (the KL divergence itself is in nats, as the proof's use of Pinsker requires)
--   - encoding: randomized algorithm → an OracleProg Bool n̄ (adaptive, real-weighted coins, every query counted, repeats included); reason: the base mission's published algorithm model; counting repeats changes no lower bound since a program can cache
--   - encoding: "makes at most Q queries" → at most Q queries on every run of positive probability; reason: the worst-case reading of the published goal and of the proof
--   - encoding: "sufficiently large n̄" → ∃ N₀, ∀ n̄ ≥ N₀, uniform in γ and K; reason: standard reading; N₀ is chosen before γ and K as the page's quantifier order requires
--   - encoding: µ̂ : {0,1}^{≤n̄} → ℝ≥0 → µ̂ : List Bool → NNReal, constrained by Assumption 3.1 only on lists of length ≤ n̄, and the program may also query longer lists; reason: those answers are unconstrained, so a guarantee for every admissible µ̂ covers the µ̂ that answers 0 there whatever µ⋆ is; such queries carry no information, and the class of achievable guarantees is the page's
--   - encoding: D_KL(ν̂‖µ⋆) ≤ K with K real → klDiv ν̂ µ⋆ ≤ ENNReal.ofReal K in [0,∞]; reason: K ≥ γ² > 0, so ofReal K is K; D_KL is +∞ off absolute continuity, as the proof uses ("D_KL(ν̂‖δ_x) is finite only if ν̂ = δ_x")
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Theorem 4.14, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_OracleProg
import Definitions.Def_TTTSampling_Supplement_klDiv

namespace TTTSampling

namespace Supplement

/-- **Theorem 4.14 (KL lower bound).**

Golowich, Moitra, Rohatgi, *The Power of Test-Time Training for Approximate Sampling*,
arXiv:2606.11437 (version of November 3, 2026), Theorem 4.14, printed p.50 (PDF p.52): "There is a
constant c > 0 so that the following holds, for any sufficiently large n̄ ∈ ℕ, parameter
γ ∈ (1/n̄, 1), and K ≥ γ². There is no randomized algorithm Alg which enjoys the following
guarantee: for any distribution µ⋆ ∈ ∆({0, 1}^n̄) and µ̂ : {0, 1}^{≤n̄} → ℝ≥0 satisfying
Assumption 3.1 with R = (1 + γ)², Alg makes at most c · n̄²γ⁶/(K² log²(n̄)·log²(2/γ)) queries to µ̂
and outputs a (random) vector X ∈ {0, 1}^n̄, according to some distribution ν̂, satisfying
D_KL(ν̂‖µ⋆) ≤ K."

**Formalization Note**
* `n̄` is written `n`; `{0, 1}` is `Bool`; a randomized algorithm is an `OracleProg Bool n`, chosen
  after `n`, `γ`, `K` and before `µ⋆`, `µ̂`. There is no class: `µ⋆` ranges over every
  distribution on `{0, 1}ⁿ`.
* "makes at most Q queries" holds on every run of positive probability. `K` is a real number.
* `D_KL` is `klDiv` (nats, `+∞` off absolute continuity); `log` in the budget is the natural
  logarithm, immaterial under `∃ c`. "Sufficiently large" is one threshold `N₀`, uniform in `γ`
  and `K`. -/
theorem theorem_4_14 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ γ : ℝ, 1 / (n : ℝ) < γ → γ < 1 → ∀ K : ℝ, γ ^ 2 ≤ K →
        ¬ ∃ A : OracleProg Bool n, ∀ μs : PMF (Fin n → Bool), ∀ μh : List Bool → NNReal,
          Assumption31 μs μh ((1 + γ) ^ 2) →
            (∀ r ∈ (A.run μh).support,
              (r.2 : ℝ) ≤ c * ((n : ℝ) ^ 2 * γ ^ 6 /
                (K ^ 2 * Real.log (n : ℝ) ^ 2 * Real.log (2 / γ) ^ 2))) ∧
            klDiv ((A.run μh).map Prod.fst) μs ≤ ENNReal.ofReal K := by sorry

end Supplement

end TTTSampling
