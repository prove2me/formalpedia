-- Prove2me | Theorems.Thm_PartialResampling_pra_exists
-- name    : PartialResampling.pra_exists
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T10:47:09.188364+00:00
-- url     : https://prove2.me/theorems/aef5fdae-d87f-41a1-9995-5984ff35ad1f
-- title:
--   Partial resampling: existence criterion (Harris–Srinivasan)
-- statement:
--   Existence form of the Moser–Tardos framework with partial resampling.
--
--   Let $X_1,\dots,X_n$ be independent random variables, where $X_i$ takes values in a finite set $\Omega_i$ and $\Pr(X_i=\omega)=p_i(\omega)>0$. An **atomic set** $Y$ is a partial assignment, i.e. a choice of values $Y(i)\in\Omega_i$ for the variables $i$ in a subset $\operatorname{supp}Y$; it *holds* on a configuration $z$ if $z_i=Y(i)$ for all $i\in\operatorname{supp}Y$, and $p^Y=\prod_{i\in\operatorname{supp}Y}p_i(Y(i))$.
--
--   Let $(B_k)_{k\in T}$ be a finite family of bad events (arbitrary predicates on configurations). For each $k$ let $Q_k\ge 0$ be a **fractional hitting set** for $B_k$: whenever $B_k$ holds on $z$,
--   $$\sum_{Y\text{ holds on }z} Q_k(Y)\ \ge\ 1 .$$
--   Call two labels $(Y,k)$ and $(Y',k')$ *related* if $k=k'$ or $\operatorname{supp}Y\cap\operatorname{supp}Y'\neq\emptyset$. Suppose there is $\mu\ge 0$ on labels such that for every label $(Y,k)$
--   $$p^Y\,Q_k(Y)\prod_{(Y',k')\text{ related to }(Y,k)}\bigl(1+\mu(Y',k')\bigr)\ \le\ \mu(Y,k).$$
--   Then there is a configuration $z$ on which no bad event $B_k$ holds.
--
--   This is the existence statement behind the partial resampling algorithm of Harris and Srinivasan (Theorem 2.6(b), applied to the multi-event encoding of Section 3.1 with one auxiliary variable per bad event, so that two resampling targets of the same event are always related). It is the engine for scale-free Chernoff-type rounding results such as the column-sparse assignment-packing theorem (Theorem 4.7), where the dependence between events is measured by the $\ell_1$ norm of the columns rather than by their number of non-zero entries.
--
--   **Formalization Note.** Atomic sets are elements of $\prod_i \mathrm{Option}(\Omega_i)$; labels are pairs (atomic set, event index); the product runs over the closed neighbourhood of the label (including the label itself). The statement is non-constructive: only the existence of a good configuration is asserted.
-- source:
--   D. G. Harris and A. Srinivasan, The Moser–Tardos framework with partial resampling, J. ACM 66(5):36 (2019), arXiv:1406.5943, Theorem 2.6(b) (p. 6) and Section 3.1 / Theorem 3.6(b) (pp. 11–14).

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
set_option autoImplicit false

namespace PartialResampling

theorem pra_exists {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
    (Ω : I → Type) [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1)
    (bad : T → (∀ i, Ω i) → Prop)
    (q : T → (∀ i, Option (Ω i)) → ℝ) (hq : ∀ k Y, 0 ≤ q k Y)
    (hhit : ∀ k z, bad k z →
      1 ≤ ∑ Y, q k Y * ∏ i, (Y i).elim 1 (fun ω => if z i = ω then 1 else 0))
    (μ : T → (∀ i, Option (Ω i)) → ℝ) (hμ : ∀ k Y, 0 ≤ μ k Y)
    (hcrit : ∀ k Y, (∏ i, (Y i).elim 1 (p i)) * q k Y *
      ∏ ℓ ∈ Finset.univ.filter (fun ℓ : (∀ i, Option (Ω i)) × T =>
        ℓ.2 = k ∨ ∃ i, (Y i).isSome ∧ (ℓ.1 i).isSome), (1 + μ ℓ.2 ℓ.1) ≤ μ k Y) :
    ∃ z : ∀ i, Ω i, ∀ k, ¬ bad k z := by sorry

end PartialResampling
