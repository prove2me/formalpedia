-- Prove2me | Theorems.Thm_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy
-- name    : Submodule.natCard_torsionBySet_pow_linear_of_finite_torsionBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/e7a5ec98-300b-58f7-a5ec-b04632cb2d39
-- title:
--   Linear growth of I^m-torsion when q-torsion is finite
-- statement:
--   Let $T$ be a commutative ring and $G$ a $T$-module (an additive commutative group with a $T$-module structure), let $q$ be a prime number, and assume that the $q$-torsion subgroup $\{x \in G : q \cdot x = 0\}$, i.e. `Submodule.torsionBy ℤ G (q : ℤ)` for the underlying $\mathbb{Z}$-module structure, is finite. Let $I$ be an ideal of $T$ containing the image of $q$ in $T$. The assertion is that there exist natural numbers $e$ and $C$, independent of $m$, such that for every $m \in \mathbb{N}$ the submodule $G[I^m] = \{x \in G : a \cdot x = 0 \text{ for all } a \in I^m\}$, written `Submodule.torsionBySet T G ↑(I ^ m)`, satisfies both $\#G[I^m] \le q^{me+C}$ and $q^{me} \le \#G[I^m] \cdot q^{C}$, where $\#$ denotes `Nat.card`. Thus the order of the $I^m$-torsion of $G$ is $q^{me + O(1)}$ with a single slope $e$ governing both bounds. No Noetherian or finiteness hypothesis is imposed on $T$ (and $I$ need not be finitely generated), and no hypothesis on $G$ beyond finiteness of its $q$-torsion; since `Nat.card` is $0$ on infinite types, the upper bound carries content only because each $G[I^m]$ is in fact finite.
--
--   This is a two-sided Hilbert–Samuel type growth estimate for torsion submodules, obtained by passing to the Pontryagin dual: it combines the linear growth of $\#\bigl(X/(I^m X)\bigr)$ for a finite module $X$ over a Noetherian ring with finite residue quotient at $q$ ([`Submodule.natCard_quotient_pow_smul_top_linear_of_finite_quotient`](thm.html#Submodule.natCard_quotient_pow_smul_top_linear_of_finite_quotient)) with the duality identity [`CharacterModule.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet`](thm.html#CharacterModule.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet). It is used in the analysis of torsion in Néron models attached to the modular curve, in particular by [`ModularCurve.jZeroNeronTorsionSheaf_growth_two_v5`](thm.html#ModularCurve.jZeroNeronTorsionSheaf_growth_two_v5), [`ModularCurve.jZeroNeronTorsionSheaf_inv_linearGrowth_v5`](thm.html#ModularCurve.jZeroNeronTorsionSheaf_inv_linearGrowth_v5) and [`ModularCurve.natCard_jZeroToricTorsion_inf_torsionBySet_pow_linearGrowth`](thm.html#ModularCurve.natCard_jZeroToricTorsion_inf_torsionBySet_pow_linearGrowth), where $T$ plays the role of a Hecke algebra and $I$ of an ideal containing $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Submodule.natCard_torsionBySet_pow_linear_of_finite_torsionBy
    (T : Type*) [CommRing T] (G : Type*) [AddCommGroup G] [Module T G]
    (q : ℕ) [Fact q.Prime] (hfin : Finite ↥(Submodule.torsionBy ℤ G (q : ℤ)))
    (I : Ideal T) (hqI : (q : T) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) * q ^ C := by sorry
