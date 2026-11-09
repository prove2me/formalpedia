-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_levin_work_investment
-- name    : PauliMixedness.Randomized.levin_work_investment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:40:24.658915+00:00
-- url     : https://prove2.me/theorems/a4e1e1bd-5ee2-4d62-8163-6474afcd2ad4
-- title:
--   Lemma A.1 — Levin work investment (corrected: k ≥ 2)
-- statement:
--   Let $k\ge2$ be an integer, $X$ uniform on a set of size $k$, $f\ge0$ any real function on that set, and $\mu\in\mathbb R$ with $\mathbb E f(X)\ge\mu$. Set $M=\lceil\log_3 k\rceil$. Then
--
--   $$\exists i\in\{1,\ldots,M\}:\quad\Pr[f(X)\ge3^{i-2}\mu]\ge\frac{3^{-i}}M.$$
--
--   Nonpositive $\mu$ is included. The finite uniform expectation and tail probability are the corresponding sum and count divided by $k$. This work-investment statement supports the Pauli influence lemma at support size $3^N$.
--
--   Differences from the source:
--   - correction: no exclusion of $k=1$ → $k\ge2$; reason: at k=1, f(1)=μ=1 satisfies every printed premise but M=0 leaves no possible index; the application k=3^N≥3 is unaffected
--   - encoding: $[k]$, base-three logarithm and uniform probability → $\operatorname{Fin}k$, $\ln k/\ln3$ and finite counts divided by k; reason: reindexing preserves all values; signed real powers retain i−2 exactly when i=1
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Lemma A.1 p.24

import Mathlib

open scoped BigOperators

namespace PauliMixedness.Randomized

/-- Lemma A.1 p.24 (corrected: k ≥ 2). At k=1, f=1 and μ=1 the printed
premises hold but the index set [ceil(log₃1)] is empty. μ may be nonpositive. -/
theorem levin_work_investment (k : ℕ) (hk : 2 ≤ k) (f : Fin k → ℝ) (μ : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hmean : μ ≤ (∑ x : Fin k, f x) / k) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ ⌈Real.log (k : ℝ) / Real.log 3⌉₊ ∧
      (3 : ℝ) ^ (-(i : ℤ)) / (⌈Real.log (k : ℝ) / Real.log 3⌉₊ : ℝ) ≤
        ((Finset.univ.filter (fun x => (3 : ℝ)^((i : ℤ) - 2) * μ ≤ f x)).card : ℝ) /
          (k : ℝ) := by sorry

end PauliMixedness.Randomized
