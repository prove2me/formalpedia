-- Prove2me | Theorems.Thm_ProConChoice_Rational_step_1
-- name    : ProConChoice.Rational.step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:26.633613+00:00
-- url     : https://prove2.me/theorems/a096ea79-3787-4d5c-849d-40d94a95a398
-- title:
--   Step 1 of the proof of Theorem 2, p. 19 — under (14), (CS) at S makes λₖ₊₁ represent p at S (15)
-- statement:
--   Let $X$ be a finite set with $n$ elements, $p$ a real function of an alternative and a set, and $1 \le k \le n - 1$. Let $\lambda_k$ be a signed weight function on the $k$-prefixes that represents $p_k$ (on all $S$ with $|S| > n - k$), and let $\lambda_{k+1}$ be a signed weight function on the $(k+1)$-prefixes that refines $\lambda_k$ by (14); in particular (RS) holds. Let $S$ be a set with $|S| = n - k$, and write $\lambda^{k+1}_{ij}$ for the weight of the $(k+1)$-prefix that lists the $i$-th ordering of $X \setminus S$ first and $x_j \in S$ in position $k + 1$. If (CS) holds at $S$,
--   $$\sum_{i \in I} \lambda^{k+1}_{ij} = q(x_j, S) \quad \text{for every } x_j \in S, \qquad \text{(CS)}$$
--   with $q$ the Möbius transform (9) of $p$, then $\lambda_{k+1}$ represents $p$ at $S$:
--   $$p(x_j, S) = \sum_{[\succ^{k+1}] \in B_{k+1}(x_j, S)} \lambda_{k+1}([\succ^{k+1}]) \quad \text{for every } x_j \in S, \qquad (15)$$
--   where $B_{k+1}(x, S)$ is the set of $(k+1)$-prefixes along which $x$ is the top of $S$.
--
--   Step 1 reduces the inductive construction of the representing weights to solving the row/column system (RS)–(CS) one set $S$ at a time.
--
--   **Formalization Note** Prefixes are injections `Fin (k+1) ↪ X`. The prefixes indexed by $(i, j)$ are those whose first $k$ entries avoid $S$ (hence are exactly $X \setminus S$, as $|X \setminus S| = k$) and whose entry `Fin.last k` is $x_j$. (RS) at $S$ is the instance of the refinement hypothesis (14) at the prefixes ordering $X \setminus S$, so it is not repeated. $|S| = n - k$ is written $|S| + k = n$.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 19, Step 1 of the proof of Theorem 2, (RS), (CS), (14), (15)

import Mathlib
import Definitions.Def_ProConChoice_Rational_RandomChoice

namespace ProConChoice.Rational

/-- Step 1 of the proof of Theorem 2 (p. 19): let `1 ≤ k ≤ n - 1`, let `λₖ` represent `pₖ`, and let
`λₖ₊₁` refine `λₖ` by (14) (this contains (RS)). If `S` has `|S| = n - k` and (CS) holds at `S`
(for each `x ∈ S`, the weights of the `(k+1)`-prefixes that list `X \ S` first and then `x` sum to
`q(x, S)`), then `λₖ₊₁` represents `p` at `S` (15). -/
theorem step_1 {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → Finset X → ℝ) (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card X)
    (lam : (Fin k ↪ X) → ℝ) (lam' : (Fin (k + 1) ↪ X) → ℝ)
    (hrep : Represents k lam p) (href : Refines k lam lam')
    (S : Finset X) (hS : S.card + k = Fintype.card X)
    (hCS : ∀ x ∈ S, ∑ π' ∈ (Finset.univ : Finset (Fin (k + 1) ↪ X)).filter
        (fun π' => (∀ i : Fin k, π' (Fin.castSucc i) ∉ S) ∧ π' (Fin.last k) = x), lam' π'
          = mobiusQ p x S) :
    ∀ x ∈ S, p x S =
      ∑ π' ∈ (Finset.univ : Finset (Fin (k + 1) ↪ X)).filter (fun π' => TopAlong π' S x),
        lam' π' := by sorry

end ProConChoice.Rational
