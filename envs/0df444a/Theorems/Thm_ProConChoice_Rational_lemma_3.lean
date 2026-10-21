-- Prove2me | Theorems.Thm_ProConChoice_Rational_lemma_3
-- name    : ProConChoice.Rational.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:21.50305+00:00
-- url     : https://prove2.me/theorems/e783fd33-0767-4fe5-bf48-07a7afcb6a9b
-- title:
--   Lemma 3, p. 17 — for a random choice function and |S| = n − k, the Möbius transforms satisfy Σ_{a∈X} |q(a,S)| ≤ 2^k
-- statement:
--   Let $X$ be a finite set with $n$ elements and let $p$ be a random choice function on $X$. Let $q$ be its Möbius transform (9), extended by $q(a, S) = q(a, S \cup \{a\})$ for $a \notin S$. Then for every choice set $S$ with $|S| = n - k$,
--   $$\sum_{a \in X} |q(a, S)| \le 2^k. \qquad (10)$$
--
--   The sum runs over all alternatives, including those outside $S$. The bound is the structural estimate that Step 3 of the proof uses to verify the hypothesis of the generalized Ford–Fulkerson theorem.
--
--   **Formalization Note** $k$ is written as $n - |S|$ (natural-number subtraction is exact because $|S| \le n$), and $S$ is nonempty, so $0 \le k \le n - 1$. The transform is `mobiusQ` from the definition `RandomChoice`, which builds in the extension to $a \notin S$.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 17, Lemma 3, eq. (10)

import Mathlib
import Definitions.Def_ProConChoice_Rational_RandomChoice

namespace ProConChoice.Rational

/-- Lemma 3 (p. 17): for a random choice function `p` with Möbius transform `q` (9) (extended by
`q(a, S) = q(a, S ∪ {a})` for `a ∉ S`), every choice set `S` with `|S| = n - k` satisfies
`∑_{a ∈ X} |q(a, S)| ≤ 2^k`; here `k = n - |S|`. -/
theorem lemma_3 {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → Finset X → ℝ) (hp : IsRCF p) (S : Finset X) (hS : S.Nonempty) :
    ∑ a : X, |mobiusQ p a S| ≤ (2 : ℝ) ^ (Fintype.card X - S.card) := by sorry

end ProConChoice.Rational
