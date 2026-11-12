-- Prove2me | Theorems.Thm_SubnormalCover_lcm_le_indexMultiplicity_mul_sigma
-- name    : SubnormalCover.lcm_le_indexMultiplicity_mul_sigma
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:45:49.296685+00:00
-- url     : https://prove2.me/theorems/ec0e3183-e2a1-42c5-8e97-949476451022
-- title:
--   The multiplicity inequality
-- statement:
--   Let $G_1,\dots,G_k$ ($k\ge 1$) and $H$ be finite-index subgroups of a group $G$, with every $G_i$ subnormal and $H$ normal in $G$, and let $a_1,\dots,a_k\in G$ be such that $\bigcup_{i} a_iG_i$ coincides with a union of left cosets of $H$. Write $h=[G:H]$, $n_i=[G:G_i]$, $g=(n_1,\dots,n_k)$, $L=[n_1,\dots,n_k]$, and let $M$ be any upper bound for the multiplicities $|\{i : n_i=n\}|$. Then case (a) of Sun's Theorem 3.2, eq. (3.8), states $\dfrac{g}{(h,g)}\le M\sum_{d\mid L/g}\dfrac1d$. **Formalization note.** Multiplying (3.8) by $(h,g)\cdot(L/g)$ and using $\sum_{d\mid m}1/d=\sigma(m)/m$ together with $g\cdot(L/g)=L$ gives the equivalent denominator-free form stated here, $L\le M\,(h,g)\,\sum_{d\mid L/g}d$; the hypotheses $0<k$ and $[G:G_i]\neq 0$ are not cosmetic, since the gcd over an empty index set is $0$ (which would truncate the natural-number division and make the claim false) and an infinite index would collapse both sides to $0$.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Theorem 3.2, eq. (3.8), case (a)

import Mathlib
import Definitions.Def_SubnormalCover_uniformCover

open Pointwise

namespace SubnormalCover

theorem lcm_le_indexMultiplicity_mul_sigma {G : Type*} [Group G] {k : ℕ} (hk : 0 < k)
    (K : Fin k → Subgroup G) (a : Fin k → G) (H : Subgroup G) [H.Normal]
    (hHfin : H.index ≠ 0) (hKfin : ∀ i, (K i).index ≠ 0) (hsn : ∀ i, (K i).IsSubnormal)
    (hunion : ∀ x ∈ ⋃ i, (a i) • (K i : Set G), ∀ y ∈ H,
      x * y ∈ ⋃ i, (a i) • (K i : Set G))
    (M : ℕ) (hM : ∀ m, indexMultiplicity K m ≤ M) :
    coverLcm K ≤
      M * Nat.gcd H.index (Finset.univ.gcd fun i => (K i).index) *
        ∑ d ∈ (coverLcm K / Finset.univ.gcd fun i => (K i).index).divisors, d := by
  sorry

end SubnormalCover
