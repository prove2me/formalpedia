-- Prove2me | Theorems.Thm_WildeQIT_ShannonCapacity_property_14_5_3
-- name    : WildeQIT.ShannonCapacity.property_14_5_3
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T18:36:01.779947+00:00
-- url     : https://prove2.me/theorems/d08d7925-4d5d-413c-82cc-e5450233d648
-- title:
--   Property 14.5.3 (Equipartition): $2^{-n(H(X,Y)+\delta)}\le p_{X^n,Y^n}(x^n,y^n)\le 2^{-n(H(X,Y)-\delta)}$
-- statement:
--   Let $(X,Y)$ be a pair of discrete random variables with joint distribution $p_{X,Y}$ on finite alphabets, with i.i.d. extension $p_{X^n,Y^n}(x^n,y^n)=\prod_{i=1}^n p_{X,Y}(x_i,y_i)$ and joint entropy $H(X,Y)$ in bits. Let $\delta>0$ and $n\ge0$. Every $\delta$-jointly typical pair $(x^n,y^n)\in T_\delta^{X^nY^n}$ has approximately uniform probability:
--
--   $$
--   2^{-n(H(X,Y)+\delta)}\le p_{X^n,Y^n}(x^n,y^n)\le 2^{-n(H(X,Y)-\delta)} . \tag{14.37}
--   $$
--
--   This is the "equipartition" of the joint asymptotic equipartition property: all jointly typical pairs are nearly equally likely.
--
--   **Formalization Note** A pair of sequences is `z : Fin n → α × β` and $p_{X^n,Y^n}(x^n,y^n)$ is `(p.iid n).prob z`; the set is the published `WildeQIT.jointTypicalSet`, $H(X,Y)$ the published `jointEntropy`; powers of 2 are real powers.
--
--   Differences from the source:
--   - encoding: pairs of probability zero are never jointly typical → `jointTypicalSet` requires positive probability explicitly; reason: Lean's $\log_2 0=0$; the set is the book's
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.5.1, Property 14.5.3, p. 433, eq. (14.37)

import Definitions.Def_WildeQIT_jointTypicalSet
import Definitions.Def_WildeQIT_jointEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 14.5.3, p. 433.
-/

namespace WildeQIT.ShannonCapacity

/-- **Property 14.5.3 (Equipartition)** (Wilde, arXiv:1106.1445v8, p. 433, eq. (14.37)).
The probability of a particular `δ`-jointly typical sequence `xⁿyⁿ` is approximately uniform:
`2^{−n(H(X,Y)+δ)} ≤ p_{Xⁿ,Yⁿ}(xⁿ, yⁿ) ≤ 2^{−n(H(X,Y)−δ)}`.

Formalization Note: the pair `(X, Y)` is a joint distribution `p` on `α × β`; a pair of
sequences is `z : Fin n → α × β` and `p_{Xⁿ,Yⁿ}(xⁿ, yⁿ) = ∏ᵢ p(zᵢ)` is `(p.iid n).prob z`;
`H(X,Y)` is the published `jointEntropy p`, in bits; powers of 2 are real powers. The bounds are
stated for every `n` and every `δ > 0`, as printed. -/
theorem property_14_5_3 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : FinDist (α × β)) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (z : Fin n → α × β)
    (hz : z ∈ jointTypicalSet p n δ) :
    (2 : ℝ) ^ (-((n : ℝ) * (jointEntropy p + δ))) ≤ (p.iid n).prob z ∧
      (p.iid n).prob z ≤ (2 : ℝ) ^ (-((n : ℝ) * (jointEntropy p - δ))) := by sorry

end WildeQIT.ShannonCapacity
