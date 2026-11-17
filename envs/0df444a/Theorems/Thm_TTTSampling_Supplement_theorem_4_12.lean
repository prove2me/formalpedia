-- Prove2me | Theorems.Thm_TTTSampling_Supplement_theorem_4_12
-- name    : TTTSampling.Supplement.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:00:56.254393+00:00
-- url     : https://prove2.me/theorems/fcde5fad-a8d0-4e32-9853-4c8692b1f2f6
-- title:
--   Theorem 4.12 — size-sensitive lower bound $\Omega(f(n,S))$ queries for classes of size $\le S$ (TV $1/16$, $R=9/4$)
-- statement:
--   In the setting of the mission (a known class $\mathcal F$ of distributions on $\{0,1\}^n$, an unknown $\mu^\star\in\mathcal F$, an oracle $\hat\mu:\{0,1\}^{\le n}\to\mathbb R_{\ge0}$ satisfying **Assumption 3.1** with parameter $R$), let
--
--   $$
--   f(n,S) = \max\left\{\min\{S,n\},\ \min\left\{\frac{\sqrt{\log S}}{\log^2(2+\log S)},\ \frac{n^2}{\log^2 n}\right\}\right\}.
--   $$
--
--   **Theorem.** There are a constant $c>0$ and a threshold $N_0$ such that for every $n\ge N_0$ and every integer $S\ge 2$ there is a class $\mathcal F$ of distributions on $\{0,1\}^n$ with $|\mathcal F|\le S$ with the following property. Every randomized algorithm which, for every $\mu^\star\in\mathcal F$ and every $\hat\mu$ satisfying Assumption 3.1 with respect to $\mu^\star$ for $R=9/4$, outputs a sample from a distribution $\hat\nu$ with $D_{\mathrm{TV}}(\mu^\star,\hat\nu)\le 1/16$, must make at least
--
--   $$
--   c\cdot f(n,S)
--   $$
--
--   queries to $\hat\mu$: there are $\mu^\star\in\mathcal F$, an admissible $\hat\mu$ and a run of positive probability on which it makes at least $c\cdot f(n,S)$ queries.
--
--   The theorem lets the class size be a free parameter: it shows a lower bound of $\tilde\Omega(\sqrt{\log|\mathcal F|})$ queries (until saturation at $n^2/\log^2 n$), matching the $\sqrt{\log|\mathcal F|}$ dependence of the upper bound of Theorem 3.2, and a lower bound linear in $\min\{S,n\}$ for small classes.
--
--   **Formalization Note** The algorithm is the base mission's `OracleProg`, chosen after $n$, $S$ and $\mathcal F$ and before $\mu^\star$ and $\hat\mu$. "Must make at least $Q$ queries" is the worst case over $\mu^\star\in\mathcal F$, admissible $\hat\mu$ and runs. $f$ is the definition `fSize` with natural logarithms.
--
--   Differences from the source:
--
--   - encoding: "must make at least c·f(n,S) queries" → some µ⋆ ∈ ℱ, some µ̂ satisfying Assumption 3.1 for R = 9/4 and some run of positive probability make at least c·f(n,S) queries; reason: worst-case query count, the reading under which Theorems 3.2 and 4.1 bound queries; the paper's proof bounds the worst case (it fixes an algorithm making at most q queries)
--   - encoding: log of unspecified base in f → natural logarithm; reason: for n, S ≥ 2 a change of base alters f by at most a constant factor, absorbed by ∃ c
--   - encoding: randomized algorithm → an OracleProg Bool n (adaptive, real-weighted coins, every query counted, repeats included); reason: the base mission's published algorithm model; counting repeats changes no lower bound since a program can cache
--   - encoding: "for all sufficiently large n and all integers S ≥ 2" → ∃ N₀, ∀ n ≥ N₀, ∀ S ∈ ℕ with 2 ≤ S; reason: standard reading; N₀ is uniform in S as the page's quantifier order requires
--   - encoding: µ̂ : {0,1}^{≤n} → ℝ≥0 → µ̂ : List Bool → NNReal, constrained by Assumption 3.1 only on lists of length ≤ n, and the program may also query longer lists; reason: those answers are unconstrained, so a guarantee for every admissible µ̂ covers the µ̂ that answers 0 there whatever µ⋆ is; such queries carry no information, and the class of achievable guarantees is the page's
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Theorem 4.12, p.48 (PDF p.50); f defined on p.47 (PDF p.49)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_OracleProg
import Definitions.Def_TTTSampling_Supplement_fSize

namespace TTTSampling

namespace Supplement

/-- **Theorem 4.12 (Size-sensitive lower bound).**

Golowich, Moitra, Rohatgi, *The Power of Test-Time Training for Approximate Sampling*,
arXiv:2606.11437 (version of November 3, 2026), Theorem 4.12, printed p.48 (PDF p.50): "There is a
constant c > 0 so that the following holds for all sufficiently large n ∈ ℕ and all integers S ≥ 2.
There exists a class of distributions ℱ ⊆ ∆({0, 1}ⁿ) with |ℱ| ≤ S such that any randomized
algorithm which enjoys the following guarantee must make at least c · f(n, S) queries to µ̂: for
every µ⋆ ∈ ℱ and every mapping µ̂ : {0, 1}^{≤n} → ℝ≥0 satisfying Assumption 3.1 with respect to µ⋆
for R = 9/4, the algorithm outputs a distribution ν̂ satisfying D_TV(µ⋆, ν̂) ≤ 1/16." The function
`f` is defined on p.47 (`fSize`).

**Formalization Note**
* `{0, 1}` is `Bool`; a randomized algorithm is an `OracleProg Bool n`, chosen after `n`, `S` and
  `ℱ`, before `µ⋆` and `µ̂`.
* "must make at least c·f(n, S) queries" is the worst case: some `µ⋆ ∈ ℱ`, some `µ̂` satisfying
  Assumption 3.1 for `R = 9/4`, and some run of positive probability make at least `c·f(n, S)`
  queries. "Sufficiently large" is one threshold `N₀`, uniform in `S`.
* `log` in `f` is the natural logarithm; under `∃ c` the base is immaterial. -/
theorem theorem_4_12 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ S : ℕ, 2 ≤ S →
      ∃ F : Finset (PMF (Fin n → Bool)), F.card ≤ S ∧
        ∀ A : OracleProg Bool n,
          (∀ μs ∈ F, ∀ μh : List Bool → NNReal, Assumption31 μs μh (9 / 4) →
            tvDist μs ((A.run μh).map Prod.fst) ≤ 1 / 16) →
          ∃ μs ∈ F, ∃ μh : List Bool → NNReal, Assumption31 μs μh (9 / 4) ∧
            ∃ r ∈ (A.run μh).support, c * fSize n S ≤ (r.2 : ℝ) := by sorry

end Supplement

end TTTSampling
