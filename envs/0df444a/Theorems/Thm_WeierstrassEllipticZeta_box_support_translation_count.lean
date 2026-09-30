-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_box_support_translation_count
-- name    : WeierstrassEllipticZeta.box_support_translation_count
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T04:23:13.958491+00:00
-- url     : https://prove2.me/theorems/178e951f-225e-4682-9162-910f6d4c98ee
-- title:
--   Exact count of admissible polynomial support translations in a box
-- statement:
--   Let $K$ be a commutative semiring, let $\sigma$ be a finite variable set, and let $p\in K[\sigma]$ be nonzero. Let $b\in\mathbb N^\sigma$ satisfy $\deg_i p\le b_i$ for every variable $i$. Define the coordinate box and its admissible support translations by
--   $$S_b=\{e\in\mathbb N^\sigma:e_i\le b_i\text{ for every }i\},\qquad
--   E(p,S_b)=\{d:e+d\in S_b\text{ for every }e\in\operatorname{supp}(p)\}.$$
--   Then $E(p,S_b)$ is finite, and
--   $$d\in E(p,S_b)\iff d_i\le b_i-\deg_i p\text{ for every }i.$$
--   Consequently,
--   $$|E(p,S_b)|=\prod_{i\in\sigma}(b_i-\deg_i p+1),\qquad
--   |S_b|=\prod_{i\in\sigma}(b_i+1).$$
--   The theorem allows an empty variable set and zero box coordinates. The hypotheses $p\ne0$ and $\deg_i p\le b_i$ are explicit; in particular, the formula is not asserted for a polynomial whose support does not fit in the box.
-- source:
--   Derived box-support counting certificate for the frontier https://prove2.me/theorems/baf9ef15-a976-4dc7-a15a-e9c68a0e6f20. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The exact counting lemma follows from coordinate support maxima and finite Finsupp interval cardinalities in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Algebra/MvPolynomial/Degrees.lean (degreeOf_eq_sup), Data/Finsupp/Interval.lean (card_Iic), and Order/Interval/Finset/Nat.lean (card_Iic). The remaining theorem asks for a sufficient box construction; it does not assert that every finite support set is a box. The uniform geometric estimate remains open.

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

open scoped Classical

noncomputable section

theorem WeierstrassEllipticZeta.box_support_translation_count
    (K σ : Type*) [CommSemiring K] [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ K) (hp : p ≠ 0) (b : σ →₀ ℕ)
    (hfit : ∀ i : σ, p.degreeOf i ≤ b i) :
    let E : Set (σ →₀ ℕ) := {d | ∀ e ∈ p.support, e + d ∈ Finset.Iic b}
    E.Finite ∧
      (∀ d : σ →₀ ℕ, d ∈ E ↔ ∀ i : σ, d i ≤ b i - p.degreeOf i) ∧
      E.ncard = ∏ i : σ, (b i - p.degreeOf i + 1) ∧
      (Finset.Iic b).card = ∏ i : σ, (b i + 1) := by sorry
