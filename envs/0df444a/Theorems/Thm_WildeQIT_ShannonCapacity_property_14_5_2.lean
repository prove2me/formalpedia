-- Prove2me | Theorems.Thm_WildeQIT_ShannonCapacity_property_14_5_2
-- name    : WildeQIT.ShannonCapacity.property_14_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:01.050508+00:00
-- url     : https://prove2.me/theorems/006662c1-de1f-4283-b934-4ae04bbd4c90
-- title:
--   Property 14.5.2 (Exponentially Smaller Cardinality): $(1-\varepsilon)2^{n(H(X,Y)-\delta)}\le|T_\delta^{X^nY^n}|\le 2^{n(H(X,Y)+\delta)}$
-- statement:
--   Let $(X,Y)$ be a pair of discrete random variables with joint distribution $p_{X,Y}$ on finite alphabets $\mathcal X\times\mathcal Y$, let $H(X,Y)$ be its joint entropy in bits, and let $T_\delta^{X^nY^n}$ be the $\delta$-jointly typical set of pairs of length-$n$ sequences. For every $\delta>0$:
--
--   1. for every block length $n$,
--   $$
--   |T_\delta^{X^nY^n}|\le 2^{n(H(X,Y)+\delta)} ; \tag{14.35}
--   $$
--   2. for every $\varepsilon\in(0,1)$ there is $N$ such that for every $n\ge N$
--   $$
--   |T_\delta^{X^nY^n}|\ge (1-\varepsilon)\,2^{n(H(X,Y)-\delta)} . \tag{14.36}
--   $$
--
--   Unless $(X,Y)$ is uniform, $H(X,Y)<\log(|\mathcal X||\mathcal Y|)$, so the jointly typical set is exponentially smaller than the set of all $(|\mathcal X||\mathcal Y|)^n$ pairs of sequences.
--
--   **Formalization Note** The cardinality is `Finset.card` of the published `WildeQIT.jointTypicalSet p n δ`, cast to $\mathbb R$; $H(X,Y)$ is the published `jointEntropy p`; powers of 2 are real powers.
--
--   Differences from the source:
--   - reading: (14.35) is printed without a quantifier on $n$ → it is stated for every $n$; reason: the bound needs no largeness of $n$ (each jointly typical pair has probability at least $2^{-n(H(X,Y)+\delta)}$), and the stronger reading is the one stated
--   - encoding: pairs of probability zero are never jointly typical → `jointTypicalSet` requires positive probability explicitly; reason: Lean's $\log_2 0=0$; the set is the book's
--   - encoding: "for sufficiently large $n$" → $\exists N,\ \forall n\ge N$; reason: standard reading
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.5.1, Property 14.5.2, p. 433, eqs. (14.35)–(14.36)

import Definitions.Def_WildeQIT_jointTypicalSet
import Definitions.Def_WildeQIT_jointEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 14.5.2, p. 433.
-/

namespace WildeQIT.ShannonCapacity

/-- **Property 14.5.2 (Exponentially Smaller Cardinality)** (Wilde, arXiv:1106.1445v8, p. 433,
eqs. (14.35)–(14.36)). For every `δ > 0`:
1. `|T_δ^{XⁿYⁿ}| ≤ 2^{n(H(X,Y)+δ)}` for every block length `n` (14.35);
2. for every `ε ∈ (0, 1)` and all sufficiently large `n`,
   `|T_δ^{XⁿYⁿ}| ≥ (1 − ε) 2^{n(H(X,Y)−δ)}` (14.36).

Formalization Note: the pair `(X, Y)` is a joint distribution `p` on `α × β`; pairs of
sequences are `Fin n → α × β`; `H(X,Y)` is the published `jointEntropy p`, in bits; powers of 2
are real powers (`Real.rpow`). The upper bound is stated for every `n` (the book's (14.35)
carries no restriction on `n`); "sufficiently large `n`" is `∃ N, ∀ n ≥ N`. -/
theorem property_14_5_2 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : FinDist (α × β)) (δ : ℝ) (hδ : 0 < δ) :
    (∀ n : ℕ, ((jointTypicalSet p n δ).card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (jointEntropy p + δ))) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n ≥ N,
      (1 - ε) * (2 : ℝ) ^ ((n : ℝ) * (jointEntropy p - δ)) ≤ ((jointTypicalSet p n δ).card : ℝ)) := by sorry

end WildeQIT.ShannonCapacity
