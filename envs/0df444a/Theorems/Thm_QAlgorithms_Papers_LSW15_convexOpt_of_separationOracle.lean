-- Prove2me | Theorems.Thm_QAlgorithms_Papers_LSW15_convexOpt_of_separationOracle
-- name    : QAlgorithms.Papers.LSW15.convexOpt_of_separationOracle
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:46:47.201735+00:00
-- url     : https://prove2.me/theorems/5cf1550d-17e4-4020-9ec9-7afc1e25415f
-- title:
--   LSW Theorem 42: convex optimization from an (η, δ)-separation oracle
-- statement:
--   This is the main convex-optimization guarantee of the Lee–Sidford–Wong cutting plane method (Theorem 42), the result cited as Theorem 5.23 in Nannicini's lecture notes.
--
--   For $r > 0$ let $B_\infty(r) = \{x \in \mathbb R^n : \|x\|_\infty \le r\}$. For a set $K \subseteq \mathbb R^n$, $\mathrm{MinWidth}(K) = \inf_{\|a\|_2 = 1} \sup_{x, y \in K} \langle a, x - y\rangle$. Given a convex $f : \mathbb R^n \to \mathbb R$, a convex set $\Gamma$ and $\eta, \delta \ge 0$, an $(\eta,\delta)$-separation oracle on $\Gamma$ for $f$ is a map that, on every input $x \in \Gamma$, either asserts $f(x) \le \min_{y \in \Gamma} f(y) + \eta$, or outputs a half space $H = \{z : c^\top z \le c^\top x + b\}$ with $c \ne 0$, $b \le \delta \|c\|_2$ and $\{z \in \Gamma : f(z) \le f(x)\} \subseteq H$.
--
--   There are universal constants $c, C > 0$ such that the following holds. Let $n \ge 1$, $R > 0$, $0 < \alpha < 1$ and $w > 0$, and put
--
--   $$\kappa = \frac{R}{w}, \qquad L = \log\Big(2 + \frac{n\kappa}{\alpha}\Big), \qquad \delta = \frac{c\, \alpha\, w}{n^{3/2} L}.$$
--
--   There is a randomized algorithm $\mathcal A$, depending only on $n, R, \alpha, w$, that queries an oracle at points of $\mathbb R^n$ and returns a point $x \in \mathbb R^n$, with the following property. For every $\eta \ge 0$, every convex $f : \mathbb R^n \to \mathbb R$, every convex set $\Omega \subseteq B_\infty(R)$ with $\mathrm{MinWidth}(\Omega) = w$ containing a global minimizer $x^*$ of $f$, and every $(\eta, \delta)$-separation oracle $O$ on $B_\infty(R)$ for $f$:
--
--   1. on every run, the returned point satisfies
--   $$f(x) - \min_{y \in \Omega} f(y) \le \eta + \alpha\Big(\sup_{y \in \Omega} f(y) - \min_{y \in \Omega} f(y)\Big);$$
--   2. the expected number of oracle calls is at most $C\, n\, L$.
--
--   The oracle only needs to satisfy its specification at points of $B_\infty(R)$. The result turns a cutting plane method into an optimization method whose number of oracle calls is linear in the dimension up to a logarithm, and many of the paper's applications rest on it.
--
--   **Formalization Note** A randomized algorithm is a probability mass function over deterministic adaptive query strategies (decision trees with real-vector queries). The paper prints $\ln\kappa$ in $\delta$. Its proof gives $\log(n\kappa/\alpha)$, and $\kappa \le 1$ is possible, which would make the printed $\delta$ non-positive, so $L = \log(2 + n\kappa/\alpha)$ is used in both places. Only the oracle part of the running time is formalized. The additional arithmetic time $n^3 \log^{O(1)}(n\kappa/\alpha)$ is omitted because the paper fixes no machine model for real arithmetic.
-- source:
--   A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization (Lee, Sidford, Wong), arXiv:1508.04874v2, Theorem 42, PDF p. 54. https://arxiv.org/abs/1508.04874v2 . PDF SHA-256: 679c7c18f3cb2a65752dbe94f6135a5d1918ed171e737bbd63b400e390c749c6.

import Definitions.Def_QAlgorithms_Defs_ConvexOpt
set_option autoImplicit false

namespace QAlgorithms.Papers.LSW15

open scoped ENNReal

/-- LSW p.54, Theorem 42 (cited by Nannicini, Theorem 5.23): convex optimization from an
`(η, δ)`-separation oracle. Let `f` be a convex function on `ℝⁿ` and `Ω ⊆ B∞(R)` a convex set
containing a minimizer `x*` of `f`. For any `0 < α < 1` one can compute `x ∈ ℝⁿ` with
`f(x) − min_{y∈Ω} f(y) ≤ η + α (max_{y∈Ω} f(y) − min_{y∈Ω} f(y))` (10.1), using an expected
`O(n log(nκ/α))` calls of an `(η, δ)`-separation oracle defined on `B∞(R)`, where
`κ = R / MinWidth(Ω)` and `δ = Θ(α MinWidth(Ω) / (n^{3/2} log(nκ/α)))`.

Formalization choices.
* The algorithm `A` depends only on `n`, `R`, `α` and `w = MinWidth(Ω)` (the proof's stopping
  width (10.2) uses `MinWidth(Ω)`; p.55: "this algorithm requires no information about `Ω`
  (other than that `Ω ⊆ B∞(R)`)"), and is fixed before `η`, `f`, `Ω` and the oracle (trap Q2).
  The universal constants `c` (oracle accuracy) and `C` (call count) come before everything.
* Output guarantee on every run (every strategy in the support), call count in expectation.
* The oracle is any function meeting Definition 2 on `Γ = B∞(R)` ("we only need the oracle
  defined on the set `B∞(R)`"); its answers at points outside `B∞(R)` are unconstrained.
* `δ = Θ(…)` is read as: oracle accuracy `δ = c · α w / (n^{3/2} L)` suffices for a universal
  `c > 0` (a `δ'`-oracle with `δ' ≤ δ` is a `δ`-oracle).
* Discrepancy with the printed statement (trap 30): the theorem prints `ln(κ)` in `δ`, but the
  proof ((10.2) and "`δ = Ω(ε/√n)`") gives `ln(nκ/α)`, and `κ ≤ 1` is possible (`Ω = B∞(R)` has
  `κ = 1/2`), which would make the printed `δ` non-positive. We use
  `L = log(2 + nκ/α)` in both `δ` and the call bound; it agrees with `log(nκ/α)` up to universal
  constants whenever `nκ/α ≥ 2` and is always positive.
* Only the oracle part of the expected running time, `O(n · SO · log(nκ/α))`, is stated, as an
  expected number of oracle calls. The additional arithmetic time `n³ log^{O(1)}(nκ/α)` is
  **not stated**: the paper fixes no machine model for arithmetic on real vectors, so that clause
  cannot be pinned.
* `max_{y∈Ω} f(y)` is `sSup (f '' Ω)`: a finite convex function on `ℝⁿ` is continuous, hence
  bounded on the bounded set `Ω`, so this is the true supremum (attained on the closure).
  `min_{y∈Ω} f(y) = f(x*)` since `x* ∈ Ω` is a global minimizer.
* `n ≥ 1` and `0 < MinWidth(Ω)` are needed for `κ = R / MinWidth(Ω)` to be defined. -/
theorem convexOpt_of_separationOracle :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (R : ℝ), 0 < R → ∀ (α : ℝ), 0 < α → α < 1 → ∀ (w : ℝ), 0 < w →
        ∃ A : RandDecisionTree (Fin n → ℝ) (Option ((Fin n → ℝ) × ℝ)) (Fin n → ℝ),
          ∀ (η : ℝ), 0 ≤ η →
          ∀ (f : (Fin n → ℝ) → ℝ), ConvexOn ℝ Set.univ f →
          ∀ (Ω : Set (Fin n → ℝ)), Convex ℝ Ω → Ω ⊆ {x | ∀ i, |x i| ≤ R} → minWidth Ω = w →
          ∀ xstar ∈ Ω, (∀ y, f xstar ≤ f y) →
          ∀ (O : (Fin n → ℝ) → Option ((Fin n → ℝ) × ℝ)),
            IsSeparationOracle η
              (c * α * w / ((n : ℝ) * Real.sqrt n *
                Real.log (2 + (n : ℝ) * (R / w) / α)))
              {x | ∀ i, |x i| ≤ R} f O →
            (∀ t ∈ A.support,
              f (t.eval O) - f xstar ≤ η + α * (sSup (f '' Ω) - f xstar)) ∧
            expectedQueries A O ≤
              ENNReal.ofReal (C * n * Real.log (2 + (n : ℝ) * (R / w) / α)) := by
  sorry

end QAlgorithms.Papers.LSW15
