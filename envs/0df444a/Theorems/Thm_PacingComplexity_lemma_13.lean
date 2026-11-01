-- Prove2me | Theorems.Thm_PacingComplexity_lemma_13
-- name    : PacingComplexity.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:05.372959+00:00
-- url     : https://prove2.me/theorems/f485c171-1803-4008-b519-54229a6fc43c
-- title:
--   Lemma 13: bounds on $\alpha(C(p,s))$ and $\alpha(D(p,s))$ (corrected: lower bound $(1-\delta)^3/2$, $n\ge3$)
-- statement:
--   Let $(A,B)$ be an $n\times n$ cost bimatrix game with all entries in $\{0,1\}$, let $G$ be the gadget SPP game built from it (with $\nu=1/(16n)$), and let $\delta=\gamma=1/n^7$. Let $(\alpha,x)$ be any $(\delta,\gamma)$-approximate pacing equilibrium of $G$, and write $\alpha(\cdot)$ for its pacing multipliers.
--   Assume $n\ge3$. Then for every $p\in\{1,2\}$ and $s\in[n]$,
--   $$
--   \frac{(1-\delta)^3}{2}\le\alpha(C(p,s))\le\frac78
--   \quad\text{and}\quad
--   (1-\delta)\,\alpha(C(p,s))\le\alpha(D(p,s))\le\frac{\alpha(C(p,s))}{1-\delta}.
--   $$
--   These bounds are the backbone of the reduction: they fix the price of the normalization good $N(p,s)_s$ and keep every buyer $C(p,s)$ close to budget-constrained.
--
--   Differences from the source:
--   - correction: (1 − δ)²/2 ≤ α(C(p, s)) → (1 − δ)³/2 ≤ α(C(p, s)); reason: the printed lower bound is false: at n = 3, A = B = 0, δ = γ = 1/3⁷, α(T) = 1 − δ, α(C(p,1)) = α(D(p,1)) = (1 − δ)³/2 ≈ 0.49931 < (1 − δ)²/2 ≈ 0.49954, α(C(p,s)) = α(D(p,s)) ≈ 0.67258 for s = 2, 3, C(p,1) winning T(p,1) at price n⁴(1 − δ)³, the dummy buying fraction ν/α of N(p,s)_s and every other good going to its top bidder, is an approximate PE (exact rational check, counterexamples.py c1); the corrected bound is attained
--   - correction: every bimatrix dimension n → n ≥ 3; reason: the upper bound 7/8 is false at n = 2: A = B = 0, δ = γ = 1/128, α(T) = 127/128, α(C(p,1)) = α(D(p,1)) = 9/10, α(C(p,2)) = α(D(p,2)) = 3/5, each good to its top bidder and the dummy buying fraction ν/α of N(p,s)_s, is an approximate PE with α(C(p,1)) = 9/10 > 7/8 (counterexamples.py c2); n = 1 is outside Definition 2 (δ = 1)
--   - encoding: p ∈ {1, 2}, s ∈ [n], named buyers and goods → a two-element index (first = player 1), Fin n, inductive buyer and good types; δ = γ = 1/n⁷ and ν = 1/(16n) written out; A, B real with entries in {0, 1}; reason: Lean convention; same instances
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Lemma 13, p.31

import Mathlib
import Definitions.Def_PacingComplexity_IsApproxPE
import Definitions.Def_PacingComplexity_GBuyer
import Definitions.Def_PacingComplexity_GGood
import Definitions.Def_PacingComplexity_gadgetValue
import Definitions.Def_PacingComplexity_gadgetBudget

namespace PacingComplexity

/-- **Lemma 13** (Chen, Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*,
arXiv:2103.13969v2, Appendix A, p.31), corrected: "For each p ∈ {1, 2} and s ∈ [n], we have
(1 − δ)^2 / 2 ≤ α(C(p, s)) ≤ 7/8 and (1 − δ) · α(C(p, s)) ≤ α(D(p, s)) ≤ α(C(p, s)) / (1 − δ)."

Let `(A, B)` be an `n × n` cost bimatrix game with entries in `{0, 1}`, `n ≥ 3`, let `G` be the
gadget game (`gadgetValue`, `gadgetBudget`) and `δ = γ = 1/n^7`. In every `(δ, γ)`-approximate
pacing equilibrium `(α, x)` of `G`, for every `p` and `s`:
`(1 − δ)^3/2 ≤ α(C(p, s)) ≤ 7/8` and `(1 − δ)α(C(p, s)) ≤ α(D(p, s)) ≤ α(C(p, s))/(1 − δ)`.

**Formalization Note** Two corrections of the printed statement. The lower bound is
`(1 − δ)^3/2`, not `(1 − δ)^2/2`: at `n = 3`, `A = B = 0` there is an approximate pacing
equilibrium with `α(C(p, 1)) = (1 − δ)^3/2 < (1 − δ)^2/2`. The upper bound `7/8` fails at `n = 2`
(`A = B = 0`, `α(C(p, 1)) = 9/10`), hence `n ≥ 3`. `n` is the bimatrix dimension; `G` has
`4n + 1` buyers. Player `1` is `p = 0`, player `2` is `p = 1`. -/
theorem lemma_13 (n : ℕ) (hn : 3 ≤ n) (A B : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hB : ∀ i j, B i j = 0 ∨ B i j = 1)
    (α : GBuyer n → ℝ) (x : GBuyer n → GGood n → ℝ)
    (hPE : IsApproxPE (gadgetValue n A B) (gadgetBudget n A B)
      (1 / (n : ℝ) ^ 7) (1 / (n : ℝ) ^ 7) α x)
    (p : Fin 2) (s : Fin n) :
    (1 - 1 / (n : ℝ) ^ 7) ^ 3 / 2 ≤ α (.C p s) ∧ α (.C p s) ≤ 7 / 8 ∧
      (1 - 1 / (n : ℝ) ^ 7) * α (.C p s) ≤ α (.D p s) ∧
      α (.D p s) ≤ α (.C p s) / (1 - 1 / (n : ℝ) ^ 7) := by sorry

end PacingComplexity
