-- Prove2me | Theorems.Thm_TTTSampling_theorem_3_2
-- name    : TTTSampling.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:44.723225+00:00
-- url     : https://prove2.me/theorems/80cea578-b359-41db-855e-54ed528b8321
-- title:
--   Theorem 3.2 (Main upper bound; corrected: $\delta$-factors at $\min(\delta,1/2)$) — TV $\delta$ with $O(n|\Sigma|R^{12}\sqrt{\log|\mathcal F|}\log\frac1\delta\log\frac{R\log|\mathcal F|}\delta)$ calls
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $n\in\mathbb N$, let $\Sigma$ be a finite alphabet, let $\mathcal F$ be a finite nonempty class of probability distributions on $\Sigma^n$, and let $R\ge1$ and $\delta\in(0,1)$. Then there is a randomized algorithm, depending only on $(n,\Sigma,\mathcal F,R,\delta)$, with the following guarantee: for every $\mu^\star\in\mathcal F$ and every oracle $\hat\mu:\Sigma^{\le n}\to\mathbb R_{\ge0}$ satisfying Assumption 3.1 with respect to $\mu^\star$ with parameter $R$, the algorithm, given query access to $\hat\mu$, outputs a sample from a distribution $\hat\nu$ on $\Sigma^n$ with
--
--   $$
--   D_{\mathrm{TV}}(\mu^\star,\hat\nu)\le\delta,
--   $$
--
--   and on every run it makes at most
--
--   $$
--   C\cdot n\cdot|\Sigma|\cdot R^{12}\cdot\sqrt{\log|\mathcal F|}\cdot\log\frac1{\delta'}\cdot\log\frac{R\log|\mathcal F|}{\delta'},\qquad \delta'=\min(\delta,1/2),
--   $$
--
--   queries to $\hat\mu$.
--
--   For a class with $\log|\mathcal F|\le n^{2-c}$ this is $o(n^2)$ queries, beating the near-quadratic lower bound that holds without knowledge of the class (Theorem 4.1): knowing that the target lies in a small known class, the abstraction of test-time training, provably speeds up sampling from an approximate density oracle.
--
--   **Formalization Note** The algorithm is a finite randomized decision tree that sees $\hat\mu$ only through counted queries and may compute freely with $\mathcal F$; it is chosen before $\mu^\star$ and $\hat\mu$.
--
--   Differences from the source:
--   - correction: the bound $O(n|\Sigma|R^{12}\sqrt{\log|\mathcal F|}\log\frac1\delta\log\frac{R\log|\mathcal F|}\delta)$ for all $\delta\in(0,1)$ → the same expression with both $\delta$-factors at $\delta'=\min(\delta,1/2)$; reason: false as printed: $\Sigma=\{0,1\}$, $R=1$, $\mathcal F$ the $2^n$ point masses, $\hat\mu=\mu^\star$, $\delta=1-2^{1-n}$; the bound is $\le C\cdot2n\sqrt{n\log2}\cdot2^{2-n}\log(2n)<1$ for large $n$, so the algorithm makes no query and outputs a fixed law $\nu$, but $D_{\mathrm{TV}}(\delta_x,\nu)=1-\nu(x)\le\delta$ for all $2^n$ strings $x$ needs total mass $\ge2$; for $\delta\le1/2$ the bound is the printed one
--   - encoding: $O(\cdot)$ → one absolute constant $C>0$ quantified before all parameters; reason: standard reading of $O(\cdot)$
--   - encoding: "there is a randomized algorithm" that knows $\mathcal F$ and queries $\hat\mu$ → an `OracleProg` (finite tree of real-weighted coins, counted queries and outputs) chosen after $(n,\Sigma,\mathcal F,R,\delta)$ and before $(\mu^\star,\hat\mu)$; reason: the algorithm may depend on the known data but not on $\mu^\star$ or $\hat\mu$, which it reaches only through queries
--   - encoding: $\mathcal F\subseteq\Delta(\Sigma^n)$ known, $\mu^\star\in\mathcal F$ → $\mathcal F$ a finite nonempty set; reason: the bound is in $|\mathcal F|$ and $\mu^\star\in\mathcal F$ makes it nonempty
--   - encoding: ratio tests $a/b \le M$, $a/b<1/M$, $1/R\le a/b\le R$ with $0/0=1$ (footnote 12) → multiplicative tests $a\le Mb$, $Ma<b$, $b\le Ra \wedge a\le Rb$; reason: realizes $a/0=\infty$ for $a>0$ and $0/0=1$ exactly; same instances
--   - encoding: "makes at most … queries" → on every run of positive probability; reason: a worst-case bound on the randomized algorithm
--   - encoding: $\log|\mathcal F|$ at $|\mathcal F|=1$ (the expression is $0\cdot\log0$) → Lean's $\log0=0$ makes the bound $0$; reason: the exact case: a zero-query sampler exists
--   - encoding: $\hat\mu:\Sigma^{\le n}\to\mathbb R_{\ge0}$ → $\hat\mu$ defined on all lists, constrained only on lists of length $\le n$; reason: queries beyond length $n$ return arbitrary values and carry no information
--   - generalization: query complexity with caching (repeated evaluations free, p.18) → every query node counts, repeats included; reason: the uncached count is at least the cached one, so the bound implies the printed one
--   - generalization: the convention $\hat\mu(\emptyset)=1$ (p.18) → no assumption on $\hat\mu(\emptyset)$ beyond (9); reason: covers more oracles; with $\hat\mu(\emptyset)=1$ it is the printed statement
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Theorem 3.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_OracleProg
import Definitions.Def_TTTSampling_qBound

namespace TTTSampling

/-- **Theorem 3.2 (Main upper bound)**, corrected: the δ-factors of the bound at `min(δ, 1/2)`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Theorem 3.2, printed
p.18 (PDF p.20): "Fix n ∈ ℕ, δ ∈ (0, 1), a finite alphabet Σ, and a known class of probability
distributions ℱ ⊆ ∆(Σⁿ). Let µ⋆ ∈ ℱ be an unknown distribution, and let µ̂ : Σ^{≤n} → ℝ≥0
satisfy Assumption 3.1 with respect to µ⋆ for some parameter R ≥ 1. Then there is a randomized
algorithm (Algorithm 3) which outputs a sample from a distribution ν̂ ∈ ∆(Σⁿ) satisfying
D_TV(µ⋆, ν̂) ≤ δ and which makes at most O(n·|Σ|·R¹²·√(log |ℱ|)·log(1/δ)·log(R log |ℱ|/δ))
queries to µ̂(·)."

**Formalization Note**
* `O(·)` is one absolute constant `C > 0`, chosen before all parameters.
* The algorithm is an `OracleProg`, chosen after `(n, Σ, ℱ, R, δ)` and before `(µ⋆, µ̂)`: it knows
  `ℱ` but not `µ⋆`, and sees `µ̂` only through counted queries. Every query counts, repeated ones
  included, and the bound holds on every run of positive probability.
* `ℱ` is a finite nonempty set of distributions (the bound is in `|ℱ|`).
* **Correction.** The bound's two δ-factors are evaluated at `δ′ = min(δ, 1/2)`. As printed, the
  bound tends to `0` as `δ → 1` while a program that makes no query cannot meet the TV clause
  (Σ = {0,1}, R = 1, ℱ the `2ⁿ` point masses, `δ = 1 − 2^{1−n}`); for `δ ≤ 1/2` the statement is
  the printed one.
* No assumption on `µ̂(∅)` beyond (9). -/
theorem theorem_3_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (α : Type) [Fintype α] [DecidableEq α] (F : Finset (PMF (Fin n → α))),
        F.Nonempty → ∀ R δ : ℝ, 1 ≤ R → 0 < δ → δ < 1 →
        ∃ A : OracleProg α n, ∀ μs ∈ F, ∀ μh : List α → NNReal, Assumption31 μs μh R →
          tvDist μs ((A.run μh).map Prod.fst) ≤ δ ∧
          ∀ r ∈ (A.run μh).support,
            (r.2 : ℝ) ≤ C * qBound n (Fintype.card α) R F.card (min δ (1 / 2)) := by sorry

end TTTSampling
