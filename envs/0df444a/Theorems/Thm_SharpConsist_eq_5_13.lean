-- Prove2me | Theorems.Thm_SharpConsist_eq_5_13
-- name    : SharpConsist.eq_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:07.95298+00:00
-- url     : https://prove2.me/theorems/f688be57-cb27-4b0e-a62b-cab86273ff2c
-- title:
--   Eq. (5.13) — a feasible comparison set
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, integers $k\ge1$, $n=(m+1)k$ and $\delta=1/(64m)$. Then
--   $$K_\delta(1,0)=c+v'(0)+\phi_m(1)+32\delta e^{-1}\ge1,$$
--   and for every $k$-set $A\subseteq X$ and every $a_0\in A$, the set $\{r\}\cup(A\setminus\{a_0\})$ has exactly $k$ elements and
--   $$f_A\bigl(\{r\}\cup(A\setminus\{a_0\})\bigr)\ge1-\frac5k.$$
--   Hence $\mathrm{OPT}_k(X\cup\{r\})\ge1-5/k$ for every hidden set.
--
--   Differences from the source:
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
--   - encoding: v, w defined on [0, ∞) → v, w defined on ℝ by the quadratic/linear piece for t ≤ T; reason: every argument the statement evaluates is nonnegative (t = ω_m y ≥ 0, z between t and s ≥ 0)
--   - encoding: v′, the derivative of v → v', the explicit piecewise formula d(T + 1 − t) for t ≤ T and d·e^{−(t−T)} for t > T; reason: it is the derivative of v at every real t (both pieces agree at t = T), so v′(0) = d(T + 1) as in the source
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.3, proof of Theorem 5.1 ("A feasible comparison set"), Eq. (5.13), p.17

import Mathlib
import Definitions.Def_SharpConsist_fA

namespace SharpConsist

/-- **Eq. (5.13): a feasible comparison set.** Fu–Zhang–Tao, *A Sharp Barrier of Consistent
Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.3, proof of
Theorem 5.1, "A feasible comparison set", Eq. (5.13), p.17. Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`,
`k ≥ 1`, `n = (m+1)k`, `δ = 1/(64m)`. At the hidden point,
`K_δ(1, 0) = c + v′(0) + ϕ_m(1) + 32δe^{−1} ≥ 1`; and for every `k`-set `A ⊆ X` and `a₀ ∈ A`, the set
`{r} ∪ (A \ {a₀})` has exactly `k` elements and `f_A({r} ∪ (A \ {a₀})) ≥ 1 − 5/k`. -/
theorem eq_5_13 (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m k n : ℕ) (hm : 32 ≤ m)
    (hk : 1 ≤ k) (hn : n = (m + 1) * k) :
    Kdelta T m 1 0 = cT T + v' T 0 + phiM m 1 + 32 * deltaM m * Real.exp (-1) ∧
    1 ≤ Kdelta T m 1 0 ∧
    ∀ (A : Finset (Fin n)), A.card = k → ∀ a₀ ∈ A,
      (insert (Fin.last n) (embedX (A.erase a₀))).card = k ∧
      1 - 5 / (k : ℝ) ≤ fA T m k A (insert (Fin.last n) (embedX (A.erase a₀))) := by sorry

end SharpConsist
