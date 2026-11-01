-- Prove2me | Theorems.Thm_WildeQIT_Compression_property_14_3_3
-- name    : WildeQIT.Compression.property_14_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:25.528878+00:00
-- url     : https://prove2.me/theorems/ff978ac0-88d2-4538-b933-7ad489a28fa1
-- title:
--   Property 14.3.3 (Equipartition): $2^{-n(H(X)+\delta)}\le p_{X^n}(x^n)\le 2^{-n(H(X)-\delta)}$ on $T_\delta^{X^n}$
-- statement:
--   Let $X$ be a discrete random variable with distribution $p_X$ on a finite alphabet $\mathcal X$, let $H(X)$ be its entropy in bits, and let $p_{X^n}(x^n)=\prod_{i=1}^np_X(x_i)$ be the i.i.d. law of length-$n$ sequences. For every $\delta>0$, every $n$ and every $\delta$-typical sequence $x^n\in T_\delta^{X^n}$,
--
--   $$
--   2^{-n(H(X)+\delta)}\le p_{X^n}(x^n)\le 2^{-n(H(X)-\delta)} .
--   $$
--
--   All typical sequences thus occur with nearly the same probability, the "equipartition" in the asymptotic equipartition property. It is the input to both cardinality bounds of Property 14.3.2.
--
--   **Formalization Note** Membership is in the published `WildeQIT.typicalSet p n δ`; the powers of 2 are real powers.
--
--   Differences from the source:
--   - reading: the quantifiers on $n$ and $\delta$ are implicit on the page → stated for every $n$ and every $\delta>0$; reason: the property follows from the definition of the typical set for each $n$
--   - encoding: sequences of probability zero are never typical → `typicalSet` requires $p_{X^n}(x^n)>0$ explicitly; reason: Lean's $\log_2 0=0$; the set is the book's
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.3, Property 14.3.3, p. 428, eq. (14.16)

import Definitions.Def_WildeQIT_typicalSet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 14.3.3, p. 428.
-/

namespace WildeQIT.Compression

/-- **Property 14.3.3 (Equipartition)** (Wilde, arXiv:1106.1445v8, p. 428, eq. (14.16)).
The probability of a `δ`-typical sequence `xⁿ` is approximately uniform:
`2^{−n(H(X)+δ)} ≤ p_{Xⁿ}(xⁿ) ≤ 2^{−n(H(X)−δ)}`.

Formalization Note: the source `X` is a distribution `p` on a finite alphabet `α`; sequences
are `Fin n → α`, entropies in bits, powers of 2 are real powers (`Real.rpow`). The statement is
for every block length `n` and every `δ > 0`. -/
theorem property_14_3_3 {α : Type} [Fintype α] (p : FinDist α) (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (x : Fin n → α) (hx : x ∈ typicalSet p n δ) :
    (2 : ℝ) ^ (-((n : ℝ) * (entropy p + δ))) ≤ (p.iid n).prob x ∧
      (p.iid n).prob x ≤ (2 : ℝ) ^ (-((n : ℝ) * (entropy p - δ))) := by sorry

end WildeQIT.Compression
