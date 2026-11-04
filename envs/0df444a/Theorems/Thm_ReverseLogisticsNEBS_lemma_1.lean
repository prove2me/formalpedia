-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_lemma_1
-- name    : ReverseLogisticsNEBS.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:50:45.561785+00:00
-- url     : https://prove2.me/theorems/8d847226-60e8-44b5-b33f-86ffc33c08d1
-- title:
--   Lemma 1 — multi-dimensional Karush lemma
-- statement:
--   Let $v_1, \dots, v_N : \mathbb R \to \mathbb R$ be convex, let $x_1 \le x_2 \le \dots \le x_N$, and define $w_1 := v_1$ and $w_j := v_j + w^-_{j-1}$; assume every $w_j$ has a finite minimizer. Then for every $0 \le n \le N - 1$,
--   $$
--   \min_{\substack{x_j \le y_j \le y_{j+1}\\ j = 1,\dots,N}} \sum_{j=1}^N v_j(y_j) = \sum_{j=1}^n w^+_j(x_j) + \min_{\substack{x_j \le y_j \le y_{j+1}\\ j = n+1,\dots,N}} \Big\{ w_{n+1}(y_{n+1}) + \sum_{j=n+2}^N v_j(y_j) \Big\}, \quad (34)
--   $$
--   with $y_{N+1} := +\infty$ and both minima attained; in particular
--   $$
--   \min_{\substack{x_j \le y_j \le y_{j+1}\\ j = 1,\dots,N}} \sum_{j=1}^N v_j(y_j) = \sum_{j=1}^N w^+_j(x_j).
--   $$
--
--   This generalizes Karush's (1959) one-dimensional decomposition $\min_{x \le \theta \le y} f(\theta) = f^+(x) + f^-(y)$ to a chain of ordered variables; it is the step that makes the value function additively convex (Theorem 3).
--
--   **Formalization Note** Indices are $0$-based in Lean; "min" is stated as `IsLeast` of the set of objective values (attained minimum).
--
--   Differences from the source:
--   - reading: for any n ≤ N in (34) → (34) for 0 ≤ n ≤ N − 1; the 'in particular' clause for n = N; reason: w_{N+1} does not exist; y_{N+1} := +∞ (paper.md item 10); at n = 0 (34) is the identity w_1 = v_1
--   - encoding: w^± applied to w_j (the notation of p.14 presupposes a finite minimizer) → every w_j has a finite minimizer (hypothesis); reason: excludes only cases where (34) is undefined (paper.md item 6)
--   - encoding: f^+(x) := f(S) if x ≤ S, f(x) otherwise; f^−(y) := f(y) − f(S) if y ≤ S, 0 otherwise → f^+(x) = inf_{θ ≥ x} f(θ), f^−(y) = inf_{θ ≤ y} f(θ) − inf f; reason: equal to the paper's formulas for convex f with a finite minimizer, independent of the choice of S
--   - encoding: min → attained minimum (IsLeast); reason: the paper's min asserts attainment
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Lemma 1, p.39

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_fPlus

namespace ReverseLogisticsNEBS

/-- **Lemma 1** (multi-dimensional Karush lemma; Angelus–Özer, SSRN 3508009, Dec. 21, 2019,
p.39). Let `v_1, …, v_N : ℝ → ℝ` be convex, `x_1 ≤ ⋯ ≤ x_N`, and
`w_1 := v_1`, `w_j := v_j + w^−_{j−1}`. Then, for every `0 ≤ n ≤ N − 1`, the minimum of
`Σ_j v_j(y_j)` over `x_j ≤ y_j ≤ y_{j+1}` (`j = 1, …, N`, `y_{N+1} := +∞`) is attained and equals
`Σ_{j ≤ n} w^+_j(x_j)` plus the (attained) minimum of `w_{n+1}(y_{n+1}) + Σ_{j ≥ n+2} v_j(y_j)`
over `x_j ≤ y_j ≤ y_{j+1}`, `j = n + 1, …, N` (34); in particular the minimum equals
`Σ_{j=1}^N w^+_j(x_j)`.

**Formalization Note.** Indices are `0`-based (`Fin N`, `karushW v j.val` is `w_{j+1}`). The
upper bound `y_{N+1} := +∞` is encoded by omitting the constraint at the top index. "For any
`n ≤ N`" is read as `0 ≤ n ≤ N − 1` for (34) (`w_{N+1}` does not exist; at `n = 0`
the identity is `w_1 = v_1`) and `n = N` for the
"in particular" clause. The `±` notation of p.14 presupposes a finite minimizer; it is assumed for
every `w_j`. "min" is attainment: `IsLeast` of the set of objective values. -/
theorem lemma_1 {N : ℕ} (v : Fin N → ℝ → ℝ) (hv : ∀ j, ConvexOn ℝ Set.univ (v j))
    (hw : ∀ j : Fin N, HasMin (karushW v j.val)) (x : Fin N → ℝ) (hx : Monotone x) :
    (∀ n, n + 1 ≤ N → ∃ m₁ m₂ : ℝ,
      IsLeast ((fun y : Fin N → ℝ => ∑ j, v j (y j)) ''
        {y | ∀ j : Fin N, x j ≤ y j ∧ ∀ i : Fin N, i.val = j.val + 1 → y j ≤ y i}) m₁ ∧
      IsLeast ((fun y : Fin N → ℝ => ∑ j : Fin N,
          if j.val < n then 0 else if j.val = n then karushW v n (y j) else v j (y j)) ''
        {y | ∀ j : Fin N, n ≤ j.val → x j ≤ y j ∧ ∀ i : Fin N, i.val = j.val + 1 → y j ≤ y i}) m₂ ∧
      m₁ = (∑ j : Fin N, if j.val < n then fPlus (karushW v j.val) (x j) else 0) + m₂) ∧
    IsLeast ((fun y : Fin N → ℝ => ∑ j, v j (y j)) ''
        {y | ∀ j : Fin N, x j ≤ y j ∧ ∀ i : Fin N, i.val = j.val + 1 → y j ≤ y i})
      (∑ j : Fin N, fPlus (karushW v j.val) (x j)) := by sorry

end ReverseLogisticsNEBS
