-- Prove2me | Theorems.Thm_ProConChoice_Rational_lemma_4
-- name    : ProConChoice.Rational.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:39.616823+00:00
-- url     : https://prove2.me/theorems/9e0a1d04-5313-48ed-ac87-a6c1dfc410aa
-- title:
--   Lemma 4 (Hoffman–Kruskal), p. 23, corrected: for A totally unimodular and b integral, every vertex of {λ : Aλ = b, −1 ≤ λ ≤ 1} is integral
-- statement:
--   Let $A$ be a real matrix with rows indexed by a finite set $M$ and columns by a finite set $N$, and let $b \in \mathbb{R}^M$. Consider the polytope
--   $$Q = \{\lambda \in \mathbb{R}^N \,:\, A\lambda = b,\ -1 \le \lambda_j \le 1 \text{ for all } j\}.$$
--   If $A$ is totally unimodular and $b$ has integer entries, then every vertex (extreme point) of $Q$ has integer coordinates.
--
--   In Section 7 this is applied to the system (RS)–(CS), whose right-hand side consists of the integer weights of the previous step and the integer Möbius transforms of a deterministic choice function.
--
--   **Formalization Note** *Corrected statement.* The paper's Lemma 4 omits the hypothesis that $b$ is integral; without it the lemma is false ($A = [1]$, $b = 1/2$: the only vertex is $1/2$). In Section 7, where the lemma is applied, $b$ is integral. Vertices are the extreme points of $Q$ (`Set.extremePoints ℝ Q`), and integer valued means every coordinate equals some integer.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 23, Lemma 4 (Hoffman & Kruskal (2010)); polyhedron Q p. 22

import Mathlib

namespace ProConChoice.Rational

/-- Lemma 4 (Hoffman–Kruskal, p. 23; corrected: `b` integral, as it is in Section 7): if `A` is
totally unimodular and `b` is integral, every vertex (extreme point) of
`Q = {λ : Aλ = b, -1 ≤ λ ≤ 1}` has integer coordinates. -/
theorem lemma_4 {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (hA : A.IsTotallyUnimodular) (b : m → ℝ) (hb : ∀ i, ∃ z : ℤ, b i = z) :
    ∀ v ∈ Set.extremePoints ℝ {x : n → ℝ | A.mulVec x = b ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1},
      ∀ j, ∃ z : ℤ, v j = z := by sorry

end ProConChoice.Rational
