-- Prove2me | Theorems.Thm_ValuationSubring_eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits
-- name    : ValuationSubring.eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/cee8ae19-e900-5d74-a591-873048e383df
-- title:
--   Uniqueness of a valuation subring extension via residue independence
-- statement:
--   Let $K$ and $K'$ be fields, $\iota\colon K\to K'$ a ring homomorphism, $n$ a natural number, and $b\colon \mathrm{Fin}\,n\to K'$ a family such that every $z\in K'$ can be written as $\sum_i \iota(c_i)\,b_i$ for some $c\colon \mathrm{Fin}\,n\to K$ (so $K'$ is spanned by $n$ elements over the image of $\iota$). Let $W$ be a valuation subring of $K$ and $U$ a valuation subring of $K'$ whose contraction along $\iota$ is $W$, i.e. $\iota^{-1}(U)=W$ as valuation subrings of $K$. Let $u\colon \mathrm{Fin}\,n\to K'$ be a family with $u_i\in U$ for all $i$, and assume the independence hypothesis: for every $c\colon \mathrm{Fin}\,n\to K$ with all $c_i\in W$ and at least one $c_i\notin W.\mathrm{nonunits}$ (that is, some $c_i$ is a unit of $W$), the element $\sum_i \iota(c_i)\,u_i$ does not lie in $U.\mathrm{nonunits}$, i.e. its value under the valuation attached to $U$ is at least $1$; since the sum lies in $U$, this says it is a unit of $U$. The conclusion is that any valuation subring $V$ of $K'$ with $\iota^{-1}(V)=W$ satisfies $V=U$; in particular $U$ is the unique such extension of $W$.
--
--   This is an elementwise form of the uniqueness half of the fundamental inequality $\sum_i e_i f_i\le [K':K]$ for extensions of a valuation to a finite extension: a family of $n$ elements of $U$ that is independent over the residue field of $W$, together with a spanning family of $n$ elements of $K'$ over $\iota(K)$, pins down the extension $U$ of $W$ completely. It is used in the determination of the valuation subrings of a Hecke roof over the Gauss centre in the analysis of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem ValuationSubring.eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits
    {K K' : Type*} [Field K] [Field K'] (ι : K →+* K') (n : ℕ)
    (b : Fin n → K') (hb : ∀ z : K', ∃ c : Fin n → K, z = ∑ i, ι (c i) * b i)
    (W : ValuationSubring K) (U : ValuationSubring K') (hU : U.comap ι = W)
    (u : Fin n → K') (hu : ∀ i, u i ∈ U)
    (hind : ∀ c : Fin n → K, (∀ i, c i ∈ W) → (∃ i, c i ∉ W.nonunits) → ∑ i, ι (c i) * u i ∉ U.nonunits)
    (V : ValuationSubring K') (hV : V.comap ι = W) :
    V = U := by sorry
