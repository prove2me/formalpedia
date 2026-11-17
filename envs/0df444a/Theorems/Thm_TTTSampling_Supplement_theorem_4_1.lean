-- Prove2me | Theorems.Thm_TTTSampling_Supplement_theorem_4_1
-- name    : TTTSampling.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:00:12.241103+00:00
-- url     : https://prove2.me/theorems/9b42854c-a03c-4c10-9342-5fc3dd0ca7b2
-- title:
--   Theorem 4.1 — main lower bound $\Omega\big(\gamma^2 n^2/(\log^2 n\,\log^2(2/\gamma))\big)$ queries for TV $\gamma/8$ at $R=(1+\gamma)^2$
-- statement:
--   Consider sampling from an unknown distribution $\mu^\star$ on $\{0,1\}^n$ that belongs to a known finite class $\mathcal F$, with access to an oracle $\hat\mu:\{0,1\}^{\le n}\to\mathbb R_{\ge 0}$ satisfying **Assumption 3.1** with parameter $R$: $\hat\mu(x)\le R\,\mu^\star(x)$ and $\mu^\star(x)\le R\,\hat\mu(x)$ at every prefix $x$ (here $\mu^\star(x)$ is the prefix marginal), and $\hat\mu(x)=\mu^\star(x)$ on full strings. A randomized algorithm is adaptive, may flip arbitrary coins and compute freely, and accesses $\hat\mu$ only through queries.
--
--   **Theorem.** There are absolute constants $c>0$ and $C>0$ and a threshold $N_0$ such that for every $n\ge N_0$ and every $\gamma\in(1/n,1)$ there is a class $\mathcal F$ of distributions on $\{0,1\}^n$ with $|\mathcal F|\le \exp(Cn^4)$ for which **no** randomized algorithm has the following guarantee: for every $\mu^\star\in\mathcal F$ and every $\hat\mu$ satisfying Assumption 3.1 with respect to $\mu^\star$ for $R=(1+\gamma)^2$, the algorithm makes at most
--
--   $$
--   \frac{c\,\gamma^2 n^2}{\log^2(n)\cdot\log^2(2/\gamma)}
--   $$
--
--   queries to $\hat\mu$ on every run and outputs a random string whose distribution $\hat\nu$ satisfies $D_{\mathrm{TV}}(\mu^\star,\hat\nu)\le\gamma/8$.
--
--   The algorithm may depend on $n$, $\gamma$ and $\mathcal F$, but not on $\mu^\star$ or $\hat\mu$. This shows that the dependence of the upper bound (Theorem 3.2, the mission's goal) on $\sqrt{\log|\mathcal F|}$ cannot be improved beyond polylogarithmic factors, and that for $\gamma$ constant roughly $n^2$ queries are needed even though $|\mathcal F|$ is only $\exp(O(n^4))$.
--
--   **Formalization Note** The algorithm is the base mission's oracle-program model (`OracleProg`), the same model as the upper bound; every query is counted, which does not affect a lower bound since a program can cache its answers. "Makes $Q$ queries" is read as "at most $Q$ queries on every run of positive probability", as the paper's proof uses it. $\log$ is the natural logarithm.
--
--   Differences from the source:
--
--   - encoding: "Alg makes cγ²n²/(log²(n)·log²(2/γ)) queries" → at most that many queries on every run of positive probability; reason: the proof (p.47) uses it as "makes at most q/2 queries", the same worst-case reading as the published goal
--   - encoding: |ℱ| ≤ exp(O(n⁴)) → ∃ absolute C > 0, chosen with c before n, with |ℱ| ≤ exp(C·n⁴); reason: standard reading of O(·) in a statement with "there is a constant c"; the constant is uniform in n and γ
--   - encoding: log of unspecified base → natural logarithm; reason: a change of base multiplies the budget by a constant factor, absorbed by ∃ c
--   - encoding: randomized algorithm → an OracleProg Bool n (adaptive, real-weighted coins, every query counted, repeats included); reason: the base mission's published algorithm model; counting repeats changes no lower bound since a program can cache
--   - encoding: "sufficiently large n" → ∃ N₀, ∀ n ≥ N₀, uniform in γ; reason: standard reading; N₀ is chosen before γ as the page's quantifier order requires
--   - encoding: µ̂ : {0,1}^{≤n} → ℝ≥0 → µ̂ : List Bool → NNReal, constrained by Assumption 3.1 only on lists of length ≤ n, and the program may also query longer lists; reason: those answers are unconstrained, so a guarantee for every admissible µ̂ covers the µ̂ that answers 0 there whatever µ⋆ is; such queries carry no information, and the class of achievable guarantees is the page's
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Theorem 4.1, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_OracleProg

namespace TTTSampling

namespace Supplement

/-- **Theorem 4.1 (main lower bound).**

Golowich, Moitra, Rohatgi, *The Power of Test-Time Training for Approximate Sampling*,
arXiv:2606.11437 (version of November 3, 2026), Theorem 4.1, printed p.32 (PDF p.34): "There is a
constant c > 0 so that the following holds, for any sufficiently large n ∈ ℕ and γ ∈ (1/n, 1).
There is a class of distributions ℱ ⊂ ∆({0, 1}ⁿ) of size |ℱ| ≤ exp(O(n⁴)) so that no randomized
algorithm Alg enjoys the following guarantee: for any distribution µ⋆ ∈ ℱ and
µ̂ : {0, 1}^{≤n} → ℝ≥0 satisfying Assumption 3.1 with respect to µ⋆ for R = (1 + γ)², Alg makes
cγ²n²/(log²(n)·log²(2/γ)) queries to µ̂ and outputs a (random) string X ∈ {0, 1}ⁿ, according to
some distribution ν̂, satisfying D_TV(µ⋆, ν̂) ≤ γ/8."

**Formalization Note**
* `{0, 1}` is `Bool`; a randomized algorithm is an `OracleProg Bool n` (adaptive, real-weighted
  coins, free computation, every query counted). It is chosen after `n`, `γ` and `ℱ`, before
  `µ⋆` and `µ̂`: it knows `ℱ` but not `µ⋆`.
* "makes Q queries" is read as "makes at most Q queries on every run of positive probability", as
  the proof uses it (p.47: "makes at most q/2 queries").
* `exp(O(n⁴))` is `exp(C·n⁴)` with an absolute `C`, chosen with `c` before `n`. "Sufficiently
  large" is one threshold `N₀`, uniform in `γ`.
* `log` is the natural logarithm; under `∃ c` the base is immaterial.
* Assumption 3.1 is the base mission's `Assumption31` (multiplicative (9), exact on full strings),
  with no condition on `µ̂(∅)`. -/
theorem theorem_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ γ : ℝ, 1 / (n : ℝ) < γ → γ < 1 →
      ∃ F : Finset (PMF (Fin n → Bool)), (F.card : ℝ) ≤ Real.exp (C * (n : ℝ) ^ 4) ∧
        ¬ ∃ A : OracleProg Bool n, ∀ μs ∈ F, ∀ μh : List Bool → NNReal,
          Assumption31 μs μh ((1 + γ) ^ 2) →
            (∀ r ∈ (A.run μh).support,
              (r.2 : ℝ) ≤ c * γ ^ 2 * (n : ℝ) ^ 2 /
                (Real.log (n : ℝ) ^ 2 * Real.log (2 / γ) ^ 2)) ∧
            tvDist μs ((A.run μh).map Prod.fst) ≤ γ / 8 := by sorry

end Supplement

end TTTSampling
