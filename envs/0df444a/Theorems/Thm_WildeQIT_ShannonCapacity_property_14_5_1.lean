-- Prove2me | Theorems.Thm_WildeQIT_ShannonCapacity_property_14_5_1
-- name    : WildeQIT.ShannonCapacity.property_14_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:35:57.939075+00:00
-- url     : https://prove2.me/theorems/b40bc74a-7567-470b-97bd-c15c69d0b94a
-- title:
--   Property 14.5.1 (Unit Probability): $\Pr\{(X^n,Y^n)\in T_\delta^{X^nY^n}\}\ge 1-\varepsilon$ for large $n$
-- statement:
--   Let $(X,Y)$ be a pair of discrete random variables with joint distribution $p_{X,Y}$ on finite alphabets $\mathcal X\times\mathcal Y$, and let a source emit $n$ independent realizations, so that $p_{X^n,Y^n}(x^n,y^n)=\prod_{i=1}^n p_{X,Y}(x_i,y_i)$. Write $T_\delta^{X^nY^n}$ for the $\delta$-jointly typical set: the pairs $(x^n,y^n)$ whose joint sample entropy $-\frac1n\log p_{X^n,Y^n}(x^n,y^n)$ is within $\delta$ of the joint entropy $H(X,Y)$ and whose components $x^n$ and $y^n$ are $\delta$-typical for $p_X$ and $p_Y$.
--
--   The jointly typical set asymptotically has probability one: for all $\varepsilon\in(0,1)$ and $\delta>0$ there is $N$ such that for every $n\ge N$
--
--   $$
--   \Pr\{(X^n,Y^n)\in T_\delta^{X^nY^n}\}\ge 1-\varepsilon .
--   $$
--
--   A long i.i.d. pair sequence is jointly typical with high probability; this is the joint form of the asymptotic equipartition property used in channel-coding arguments.
--
--   **Formalization Note** A pair of sequences is a sequence of pairs `Fin n → α × β`, its law is `p.iid n`, and the jointly typical set is the published `WildeQIT.jointTypicalSet p n δ` (Definitions 14.5.1–14.5.3). Logarithms are base 2.
--
--   Differences from the source:
--   - encoding: pairs of probability zero have joint sample entropy $+\infty$ and are never jointly typical → `jointTypicalSet` requires $p_{X^n,Y^n}(x^n,y^n)>0$ explicitly; reason: Lean's $\log_2 0=0$ would otherwise give them sample entropy $0$; the set is the book's
--   - encoding: "for sufficiently large $n$" → $\exists N,\ \forall n\ge N$; reason: standard reading
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.5.1, Property 14.5.1, p. 432, eq. (14.34); Definitions 14.5.1–14.5.3, pp. 431–432

import Definitions.Def_WildeQIT_jointTypicalSet

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 14.5.1, p. 432.
-/

namespace WildeQIT.ShannonCapacity

/-- **Property 14.5.1 (Unit Probability)** (Wilde, arXiv:1106.1445v8, p. 432, eq. (14.34)).
The jointly typical set asymptotically has probability one: for all `ε ∈ (0, 1)`, `δ > 0` and
all sufficiently large `n`, `Pr{(Xⁿ, Yⁿ) ∈ T_δ^{XⁿYⁿ}} ≥ 1 − ε`.

Formalization Note: the pair `(X, Y)` is a joint distribution `p` on `α × β` (finite
alphabets); a pair of sequences `(xⁿ, yⁿ)` is a sequence of pairs `Fin n → α × β`, whose i.i.d.
law is `p.iid n` (14.32). Logarithms are base 2. "Sufficiently large `n`" is `∃ N, ∀ n ≥ N`. The
jointly typical set is the published `jointTypicalSet p n δ` (Definitions 14.5.1–14.5.3), which
contains only pairs of positive probability. -/
theorem property_14_5_1 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : FinDist (α × β)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
      1 - ε ≤ (p.iid n).probOf (jointTypicalSet p n δ) := by sorry

end WildeQIT.ShannonCapacity
