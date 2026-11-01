-- Prove2me | Theorems.Thm_WildeQIT_ShannonCapacity_property_14_5_4
-- name    : WildeQIT.ShannonCapacity.property_14_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:02.902263+00:00
-- url     : https://prove2.me/theorems/be75f782-0978-44b7-899a-daf2d2d27b84
-- title:
--   Property 14.5.4 (Probability of Joint Typicality): $\Pr\{(\tilde X^n,\tilde Y^n)\in T_\delta^{X^nY^n}\}\le 2^{-n(I(X;Y)-3\delta)}$
-- statement:
--   Let $(X,Y)$ be a pair of discrete random variables with joint distribution $p_{X,Y}$ on finite alphabets, let $I(X;Y)$ be their mutual information in bits, and let $T_\delta^{X^nY^n}$ be the $\delta$-jointly typical set. Let $\tilde X^n$ and $\tilde Y^n$ be independent random sequences distributed according to the marginal laws $p_{X^n}(x^n)=\prod_i p_X(x_i)$ and $p_{Y^n}(y^n)=\prod_i p_Y(y_i)$, so that $(\tilde X^n,\tilde Y^n)\sim p_{X^n}(x^n)p_{Y^n}(y^n)$. Then for every $\delta>0$ and every $n$
--
--   $$
--   \Pr\{(\tilde X^n,\tilde Y^n)\in T_\delta^{X^nY^n}\}=\sum_{(x^n,y^n)\in T_\delta^{X^nY^n}}p_{X^n}(x^n)\,p_{Y^n}(y^n)\le 2^{-n(I(X;Y)-3\delta)} .
--   $$
--
--   Two sequences drawn independently from the marginals look jointly typical with probability about $2^{-nI(X;Y)}$; this is the interpretation of mutual information behind its role as the channel capacity.
--
--   **Formalization Note** A pair of sequences is `z : Fin n → α × β` with components `seqFst z` and `seqSnd z`; $p_{X^n}$ and $p_{Y^n}$ are `p.fst.iid n` and `p.snd.iid n`; $I(X;Y)$ is the published `mutualInfo p`; powers of 2 are real powers.
--
--   Differences from the source:
--   - reading: (14.39) is printed without a quantifier on $n$ → it is stated for every $n$; reason: the bound in the hint (14.40) needs no largeness of $n$, and the stronger reading is the one stated
--   - encoding: pairs of probability zero are never jointly typical → `jointTypicalSet` requires positive probability explicitly; reason: Lean's $\log_2 0=0$; the set is the book's
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.5.1, Property 14.5.4, p. 434, eqs. (14.38)–(14.40)

import Definitions.Def_WildeQIT_jointTypicalSet
import Definitions.Def_WildeQIT_mutualInfo
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 14.5.4, p. 434.
-/

namespace WildeQIT.ShannonCapacity

/-- **Property 14.5.4 (Probability of Joint Typicality)** (Wilde, arXiv:1106.1445v8, p. 434,
eqs. (14.38)–(14.40)). Let `X̃ⁿ` and `Ỹⁿ` be independent, distributed according to the marginal
laws `p_{Xⁿ}` and `p_{Yⁿ}` of the i.i.d. pair `(Xⁿ, Yⁿ)`. Then
`Pr{(X̃ⁿ, Ỹⁿ) ∈ T_δ^{XⁿYⁿ}} ≤ 2^{−n(I(X;Y)−3δ)}`.

Formalization Note: the pair `(X, Y)` is a joint distribution `p` on `α × β`; a pair of
sequences is `z : Fin n → α × β` with components `seqFst z = xⁿ` and `seqSnd z = yⁿ`, so the
probability on the left is `∑_{z ∈ T_δ^{XⁿYⁿ}} p_{Xⁿ}(xⁿ) p_{Yⁿ}(yⁿ)` (14.40), with
`p_{Xⁿ} = p.fst.iid n` and `p_{Yⁿ} = p.snd.iid n`. `I(X;Y)` is the published `mutualInfo p`, in
bits. The bound is stated for every `n` and every `δ > 0`, as printed. -/
theorem property_14_5_4 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : FinDist (α × β)) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∑ z ∈ jointTypicalSet p n δ, (p.fst.iid n).prob (seqFst z) * (p.snd.iid n).prob (seqSnd z) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo p - 3 * δ))) := by sorry

end WildeQIT.ShannonCapacity
