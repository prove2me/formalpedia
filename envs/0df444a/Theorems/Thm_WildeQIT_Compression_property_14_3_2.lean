-- Prove2me | Theorems.Thm_WildeQIT_Compression_property_14_3_2
-- name    : WildeQIT.Compression.property_14_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:31.285343+00:00
-- url     : https://prove2.me/theorems/23214839-e52e-47c5-a057-9299b6bc6509
-- title:
--   Property 14.3.2 (Exponentially Smaller Cardinality): $(1-\varepsilon)2^{n(H(X)-\delta)}\le|T_\delta^{X^n}|\le 2^{n(H(X)+\delta)}$
-- statement:
--   Let $X$ be a discrete random variable with distribution $p_X$ on a finite alphabet $\mathcal X$, let $H(X)$ be its entropy in bits, and let $T_\delta^{X^n}\subseteq\mathcal X^n$ be the $\delta$-typical set of length-$n$ sequences of the i.i.d. source $X^n$. For every $\delta>0$:
--
--   1. for every block length $n$,
--   $$
--   |T_\delta^{X^n}|\le 2^{n(H(X)+\delta)} ;
--   $$
--   2. for every $\varepsilon\in(0,1)$ there is $N$ such that for every $n\ge N$
--   $$
--   |T_\delta^{X^n}|\ge (1-\varepsilon)\,2^{n(H(X)-\delta)} .
--   $$
--
--   Since $|\mathcal X|^n=2^{n\log|\mathcal X|}$ and $H(X)<\log|\mathcal X|$ unless $X$ is uniform, the typical set is exponentially smaller than the set of all sequences while carrying almost all of the probability. The upper bound fixes the number of bits a compression code needs.
--
--   **Formalization Note** The cardinality is `Finset.card` of the published `WildeQIT.typicalSet p n δ`, cast to $\mathbb R$; the powers of 2 are real powers.
--
--   Differences from the source:
--   - reading: (14.14) is printed without a quantifier on $n$ → it is stated for every $n$; reason: the book's proof (14.24) uses no largeness of $n$, and the stronger reading is the one stated
--   - encoding: sequences of probability zero are never typical → `typicalSet` requires $p_{X^n}(x^n)>0$ explicitly; reason: Lean's $\log_2 0=0$; the set is the book's
--   - encoding: "for sufficiently large $n$" → $\exists N,\ \forall n\ge N$; reason: standard reading
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.3, Property 14.3.2, p. 427, eqs. (14.14)–(14.15)

import Definitions.Def_WildeQIT_typicalSet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 14.3.2, p. 427.
-/

namespace WildeQIT.Compression

/-- **Property 14.3.2 (Exponentially Smaller Cardinality)** (Wilde, arXiv:1106.1445v8, p. 427,
eqs. (14.14)–(14.15)). For every `δ > 0`:
1. `|T_δ^{Xⁿ}| ≤ 2^{n(H(X)+δ)}` for every block length `n`;
2. for every `ε ∈ (0, 1)` and all sufficiently large `n`, `|T_δ^{Xⁿ}| ≥ (1 − ε) 2^{n(H(X)−δ)}`.

Formalization Note: the source `X` is a distribution `p` on a finite alphabet `α`; sequences
are `Fin n → α`, entropies in bits, powers of 2 are real powers (`Real.rpow`). The upper bound
is stated for every `n` (the book's (14.14) carries no restriction on `n`); "sufficiently large
`n`" is `∃ N, ∀ n ≥ N`. -/
theorem property_14_3_2 {α : Type} [Fintype α] (p : FinDist α) (δ : ℝ) (hδ : 0 < δ) :
    (∀ n : ℕ, ((typicalSet p n δ).card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (entropy p + δ))) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n ≥ N,
      (1 - ε) * (2 : ℝ) ^ ((n : ℝ) * (entropy p - δ)) ≤ ((typicalSet p n δ).card : ℝ)) := by sorry

end WildeQIT.Compression
