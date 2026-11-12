-- Prove2me | Theorems.Thm_SubnormalCover_primeFactors_normalCore_index
-- name    : SubnormalCover.primeFactors_normalCore_index
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:43:42.479043+00:00
-- url     : https://prove2.me/theorems/299bf783-208f-45e6-b8e9-f262580f3c1d
-- title:
--   Prime divisors of the index of the normal core
-- statement:
--   Let $H$ be a **subnormal** subgroup of finite index of a group $G$, and let $H_G$ be its normal core, the largest normal subgroup of $G$ contained in $H$. Then the finite quotient $G/H_G$ and the index $[G:H]$ have exactly the same prime divisors: $P(|G/H_G|)=P([G:H])$. The inclusion $P([G:H])\subseteq P(|G/H_G|)$ is free for any subgroup, since $[G:H]$ divides $[G:H_G]$; the reverse inclusion is the content, and it follows from Lemma 2.1 applied to the conjugates $a_iHa_i^{-1}$, whose intersection is $H_G$ and each of which is subnormal of index $[G:H]$. *Formalization note:* $|G/H_G|$ is written `H.normalCore.index`, which is definitionally `Nat.card (G ⧸ H.normalCore)`; the finite-index hypothesis guarantees $H_G$ also has finite index (`Subgroup.finiteIndex_normalCore`), so neither `Nat.primeFactors` argument is the junk value $0$.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Lemma 2.2, eq. (2.2)

import Mathlib

namespace SubnormalCover

/-- **Sun, Lemma 2.2 / equation (2.2).**

If `H` is a *subnormal* subgroup of finite index of a group `G`, then the order of the quotient
`G / H_G` by the normal core `H_G` of `H` has exactly the same prime divisors as the index
`[G : H]`, i.e. `P(|G / H_G|) = P([G : H])`.

Here `|G / H_G|` is spelled `H.normalCore.index`, which is definitionally `Nat.card (G ⧸ H.normalCore)`.
The inclusion `P([G : H]) ⊆ P(|G / H_G|)` holds for every subgroup, since `[G : H]` divides
`[G : H_G]`; subnormality is what makes the reverse inclusion true. -/
theorem primeFactors_normalCore_index {G : Type*} [Group G] (H : Subgroup G)
    (hsn : H.IsSubnormal) (hfin : H.FiniteIndex) :
    H.normalCore.index.primeFactors = H.index.primeFactors := by
  sorry

end SubnormalCover
