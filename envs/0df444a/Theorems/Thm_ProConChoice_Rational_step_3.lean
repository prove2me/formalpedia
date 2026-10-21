-- Prove2me | Theorems.Thm_ProConChoice_Rational_step_3
-- name    : ProConChoice.Rational.step_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:25.382592+00:00
-- url     : https://prove2.me/theorems/da927733-dfb1-4eb0-8ef3-44fb6100a37c
-- title:
--   Step 3 of the proof of Theorem 2, eq. (29) under (33), pp. 21–22 — Σᵢ|λₖ([≻ᵏᵢ])| + Σⱼ|q(xⱼ,S)| ≤ 2·k! for 2 < k < n
-- statement:
--   Let $X$ be a finite set with $n$ elements, $p$ a random choice function on $X$ with Möbius transform $q$, and $2 < k < n$. Let $\lambda_k$ be a signed weight function on the $k$-prefixes that represents $p_k$ and satisfies the bound (33) inherited from item 3 of Theorem 3 at the previous step: for every set $T$ with $|T| = n - k + 1$ and every $y \in T$,
--   $$\sum_{[\succ^k_i] \in Q_k(y, T)} |\lambda_k([\succ^k_i])| \ \le\ |q(y, T)| + \frac{(k-1)!}{n - k + 1}, \qquad (33)$$
--   where $Q_k(y, T)$ is the set of $k$-prefixes that list the $k - 1$ alternatives of $X \setminus T$ first and $y$ in position $k$. Then for every choice set $S$ with $|S| = n - k$,
--   $$\sum_{i \in I} |\lambda_k([\succ^k_i])| + \sum_{x_j \in S} |q(x_j, S)| \ \le\ 2\,k!, \qquad (29)$$
--   the first sum running over the $k!$ prefixes $[\succ^k_i]$ that order $X \setminus S$.
--
--   Inequality (29) is the second hypothesis of the generalized Ford–Fulkerson theorem for the system (RS)–(CS) at $S$, with $m = k!$ rows.
--
--   **Formalization Note** $Q_k(y, T)$ is the set of injections `Fin k ↪ X` with entry $k - 1$ (index base $0$) equal to $y$ and entries $0, \dots, k-2$ outside $T$. The denominator $n - k + 1$ is a real number, positive since $k < n$. The case $k = 2$, where the paper has $|\lambda_2| = |q(y, T)|$ without slack, is not included: with the slack term of (33) the inequality would not follow at $k = 2$, and the paper's final inequality $2^k + k!/(n-k+1) \le 2\,k!$ is stated for $2 < k < n$.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 21, Step 3 of the proof of Theorem 2, eq. (29); p. 22, eq. (33) and the inequality 2^k + k!/(n−k+1) ≤ 2k! for 2 < k < n

import Mathlib
import Definitions.Def_ProConChoice_Rational_RandomChoice

namespace ProConChoice.Rational

/-- Step 3 of the proof of Theorem 2, eq. (29) under (33) (pp. 21–22): let `p` be a random choice
function, `2 < k < n`, and `λₖ` represent `pₖ`. Assume (33): for every `T` with `|T| = n - k + 1`
and `y ∈ T`, the absolute weights of the `k`-prefixes listing `X \ T` first and `y` in position
`k` sum to at most `|q(y, T)| + (k-1)!/(n-k+1)`. Then for every `S` with `|S| = n - k`,
`∑ |λₖ([≻ᵏᵢ])| + ∑_{x ∈ S} |q(x, S)| ≤ 2·k!`, the first sum over the `k!` prefixes ordering
`X \ S`. -/
theorem step_3 {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → Finset X → ℝ) (hp : IsRCF p) (k : ℕ) (hk : 2 < k) (hkn : k < Fintype.card X)
    (lam : (Fin k ↪ X) → ℝ) (hrep : Represents k lam p)
    (h33 : ∀ T : Finset X, T.card + k = Fintype.card X + 1 → ∀ y ∈ T,
      ∑ π ∈ (Finset.univ : Finset (Fin k ↪ X)).filter
          (fun π => π ⟨k - 1, by omega⟩ = y ∧ ∀ i : Fin k, (i : ℕ) < k - 1 → π i ∉ T), |lam π|
        ≤ |mobiusQ p y T| + ((k - 1).factorial : ℝ) / ((Fintype.card X : ℝ) - k + 1))
    (S : Finset X) (hS : S.card + k = Fintype.card X) :
    ∑ π ∈ (Finset.univ : Finset (Fin k ↪ X)).filter (fun π => ∀ i, π i ∉ S), |lam π|
      + ∑ x ∈ S, |mobiusQ p x S| ≤ 2 * (k.factorial : ℝ) := by sorry

end ProConChoice.Rational
