-- Prove2me | Theorems.Thm_WildeQIT_Compression_property_14_3_1
-- name    : WildeQIT.Compression.property_14_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:27.364701+00:00
-- url     : https://prove2.me/theorems/c65df042-4eb5-41b9-b665-94b78f3bc30f
-- title:
--   Property 14.3.1 (Unit Probability): $\Pr\{X^n\in T_\delta^{X^n}\}\ge 1-\varepsilon$ for large $n$
-- statement:
--   Let $X$ be a discrete random variable with distribution $p_X$ on a finite alphabet $\mathcal X$, and let an i.i.d. source emit $X^n=X_1\cdots X_n$, so that $p_{X^n}(x^n)=\prod_{i=1}^n p_X(x_i)$. Write $H(X)$ for the entropy of $X$ in bits and $T_\delta^{X^n}$ for the $\delta$-typical set, the set of sequences $x^n$ whose sample entropy $-\frac1n\log p_{X^n}(x^n)$ lies within $\delta$ of $H(X)$.
--
--   The typical set asymptotically has probability one: for all $\varepsilon\in(0,1)$ and $\delta>0$ there is $N$ such that for every $n\ge N$
--
--   $$
--   \Pr\{X^n\in T_\delta^{X^n}\}=\sum_{x^n\in T_\delta^{X^n}}p_{X^n}(x^n)\ge 1-\varepsilon .
--   $$
--
--   This is the "unit probability" half of the asymptotic equipartition property: a long i.i.d. sequence is typical with high probability. It drives the direct part of Shannon's compression theorem.
--
--   **Formalization Note** Sequences of length $n$ are functions `Fin n → α`, the i.i.d. law is `p.iid n`, and the typical set is the published `WildeQIT.typicalSet p n δ` (Definition 14.2.3). Logarithms are base 2.
--
--   Differences from the source:
--   - encoding: sequences of probability zero have sample entropy $+\infty$ and are never typical → `typicalSet` requires $p_{X^n}(x^n)>0$ explicitly; reason: Lean's $\log_2 0=0$ would otherwise give them sample entropy $0$; the set is the book's
--   - encoding: "for sufficiently large $n$" → $\exists N,\ \forall n\ge N$; reason: standard reading
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.3, Property 14.3.1, p. 427, eq. (14.13); Definitions 14.2.1–14.2.3, p. 426

import Definitions.Def_WildeQIT_typicalSet

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 14.3.1, p. 427.
-/

namespace WildeQIT.Compression

/-- **Property 14.3.1 (Unit Probability)** (Wilde, arXiv:1106.1445v8, p. 427, eq. (14.13)).
The typical set asymptotically has probability one: for all `ε ∈ (0, 1)`, `δ > 0` and all
sufficiently large `n`, `Pr{Xⁿ ∈ T_δ^{Xⁿ}} = ∑_{xⁿ ∈ T_δ^{Xⁿ}} p_{Xⁿ}(xⁿ) ≥ 1 − ε`.

Formalization Note: the source `X` is a distribution `p` on a finite alphabet `α`; sequences
are `Fin n → α`, logarithms are base 2. "Sufficiently large `n`" is `∃ N, ∀ n ≥ N`. The typical
set `typicalSet p n δ` (Definition 14.2.3) contains only sequences of positive probability. -/
theorem property_14_3_1 {α : Type} [Fintype α] (p : FinDist α) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
      1 - ε ≤ (p.iid n).probOf (typicalSet p n δ) := by sorry

end WildeQIT.Compression
