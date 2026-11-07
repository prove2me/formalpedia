-- Prove2me | Theorems.Thm_PRUPermLayer_theorem_1_1
-- name    : PRUPermLayer.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:31:44.637197+00:00
-- url     : https://prove2.me/theorems/31cfe526-b2dd-4372-85c3-88c7ed41841b
-- title:
--   Theorem 1.1 — adaptive forward security of $PL$: $\mathrm{Adv}^{\mathrm{opt}}_t(PL) = (1+o(1))\binom t2(2/3)^n$
-- statement:
--   Let $N = 2^n$, and let $PL$ be a uniformly random permutation unitary $P$ preceded by a layer $L = C_1 \otimes \cdots \otimes C_n$ of independent uniformly random single-qubit Clifford gates.
--
--   1. For every integer $t \ge 2$ with $t^2 \le N/4$, every algorithm that makes $t$ adaptive forward queries distinguishes $PL$ from a Haar-random unitary with advantage at most
--   $$
--   \min\Big\{1,\ 2t(t-1)\Big(\frac23\Big)^n + \frac{32\,t^2}{N}\Big\}.
--   $$
--   2. For every polynomial $p$, as $n \to \infty$, uniformly over integers $2 \le t \le p(n)$,
--   $$
--   \mathrm{Adv}^{\mathrm{opt}}_t(PL) = (1 + o(1))\binom t2\Big(\frac23\Big)^n .
--   $$
--   That is: for every $\varepsilon > 0$ there is $n_0$ such that for all $n \ge n_0$ and all integers $2 \le t \le p(n)$,
--   $$
--   \Big|\mathrm{Adv}^{\mathrm{opt}}_t(PL) - \binom t2\Big(\frac23\Big)^n\Big| \le \varepsilon \binom t2\Big(\frac23\Big)^n .
--   $$
--
--   One layer of independent single-qubit gates in front of a random permutation suffices for security against polynomially many adaptive forward queries, and the collision test among the $\binom t2$ pairs of queries is optimal up to a factor $1 + o(1)$.
--
--   Differences from the source:
--   - encoding: $t^2 \le N/4$ → $4t^2 \le 2^n$ in $\mathbb N$; reason: equivalent for integers
--   - reading: $(1+o(1))\binom t2 (2/3)^n$ as $n\to\infty$, uniformly over $2 \le t \le p(n)$ → for every $\varepsilon > 0$ there is $n_0$ (depending on $p$, $\varepsilon$) with $|\mathrm{Adv}^{\mathrm{opt}}_t - \binom t2(2/3)^n| \le \varepsilon\binom t2(2/3)^n$ for all $n \ge n_0$ and $2 \le t \le p(n)$; reason: this is the definition of the phrase; two-sided
--   - generalization: every polynomial $p$ → every polynomial $p$ with real coefficients; reason: integer polynomials are among them; every real polynomial is dominated by an integer one for $n \ge 1$
--   - generalization: an algorithm that measures and outputs one bit, with a workspace and a reference register → any final effect $0 \preceq M \preceq I$ and any number $m$ of extra qubits; reason: effects include projective measurements, and every finite workspace embeds in qubits, so the source's algorithms are among the Lean ones; conversely an effect is a projector on one more workspace qubit after a unitary (Naimark dilation), absorbed into $A_t$, so $\mathrm{Adv}^{\mathrm{opt}}_t$ is the same supremum and part (ii) specializes to the source's
--   - encoding: uniform Clifford gates modulo phase; $\mathrm{Adv}^{\mathrm{opt}}_t$ a supremum → 24 fixed representatives; a real supremum over a family bounded by $1$; reason: a phase does not change acceptance probabilities; the bounded supremum is the least upper bound
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Theorem 1.1, p.2 (PDF p.4); proof §5.1, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_PRUPermLayer_advantage
import Definitions.Def_PRUPermLayer_advOpt
import Definitions.Def_PRUPermLayer_plEnsemble
import Definitions.Def_PRUPermLayer_haar
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Theorem 1.1** (adaptive forward security; Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Theorem 1.1, p.2 (PDF p.4); proof §5.1,
pp.19–20 (PDF pp.21–22)). Let each `Cᵢ` be a uniformly random single-qubit Clifford gate and
`N = 2ⁿ`.

(i) For every integer `t ≥ 2` with `t² ≤ N/4`, every algorithm that makes `t` adaptive forward
queries distinguishes `PL` from a Haar-random unitary with advantage at most
`min{1, 2t(t − 1)(2/3)ⁿ + 32t²/N}`.

(ii) For every polynomial `p`, as `n → ∞`, uniformly over integers `2 ≤ t ≤ p(n)`,
`Adv^opt_t(PL) = (1 + o(1)) C(t, 2) (2/3)ⁿ`.

**Formalization Note** `t² ≤ N/4` is `4 * t ^ 2 ≤ 2 ^ n` in `ℕ`. Part (ii) is the two-sided
`ε`–`n₀` form of `(1 + o(1))` uniformly in `t`: for every `ε > 0` there is `n₀`, depending only on
`p` and `ε`, with `|Adv^opt_t(PL) − C(t,2)(2/3)ⁿ| ≤ ε C(t,2)(2/3)ⁿ` for all `n ≥ n₀` and all
integers `2 ≤ t ≤ p(n)`. `p` ranges over real polynomials. Algorithms are `FwdAlg` (any number of
workspace qubits, any final effect). -/
theorem theorem_1_1 :
    (∀ n t : ℕ, 2 ≤ t → 4 * t ^ 2 ≤ 2 ^ n → ∀ alg : FwdAlg n t,
      advantage alg (plEnsemble n) (haar n) ≤
        min 1 (2 * t * ((t : ℝ) - 1) * (2 / 3 : ℝ) ^ n + 32 * (t : ℝ) ^ 2 / 2 ^ n)) ∧
    (∀ p : Polynomial ℝ, ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℕ, 2 ≤ t → (t : ℝ) ≤ p.eval (n : ℝ) →
      |advOpt n t (plEnsemble n) - (t.choose 2 : ℝ) * (2 / 3 : ℝ) ^ n| ≤
        ε * ((t.choose 2 : ℝ) * (2 / 3 : ℝ) ^ n)) := by sorry

end PRUPermLayer
