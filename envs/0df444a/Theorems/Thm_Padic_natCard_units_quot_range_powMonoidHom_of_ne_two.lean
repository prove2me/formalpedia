-- Prove2me | Theorems.Thm_Padic_natCard_units_quot_range_powMonoidHom_of_ne_two
-- name    : Padic.natCard_units_quot_range_powMonoidHom_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/ebaa33f1-5138-52de-8dc6-70fec03654b0
-- title:
--   #(ℚₚ^×/(ℚₚ^×)ᵖ) = p² for odd p
-- statement:
--   Let $p$ be a natural number carrying the instance that it is prime, and assume $p \neq 2$. Consider the multiplicative group $(\mathbb{Q}_p)^\times$ of units of the field of $p$-adic numbers, and the monoid endomorphism $x \mapsto x^p$ on it, i.e. `powMonoidHom p` viewed as a homomorphism $(\mathbb{Q}_p)^\times \to (\mathbb{Q}_p)^\times$; its range is the subgroup $((\mathbb{Q}_p)^\times)^p$ of $p$-th powers. The assertion is that the quotient group $(\mathbb{Q}_p)^\times / ((\mathbb{Q}_p)^\times)^p$ has `Nat.card` equal to $p^2$. Since `Nat.card` takes the value $0$ on infinite types, the statement in particular records that this quotient is finite, of order exactly $p^2$. This is the cardinality form of the corresponding index statement for the subgroup of $p$-th powers.
--
--   For an odd prime $p$ the group $\mathbb{Q}_p^\times \cong p^{\mathbb{Z}} \times \mathbb{Z}_p^\times$ has $p$-th power quotient of order $p^2$, the two factors coming from the valuation and from the principal units $1 + p\mathbb{Z}_p$ (the residual factor $\mathbb{F}_p^\times$ being $p$-divisible). The result is used in the local computations bounding the dimensions of spaces of cocycles and of continuous cohomology classes for the cyclotomic character at a prime, via [`groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two`](thm.html#groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two) and [`groupCohomology.finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal`](thm.html#groupCohomology.finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_natCard_units_quot_range_powMonoidHom_of_ne_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Padic.natCard_units_quot_range_powMonoidHom_of_ne_two {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) :
    Nat.card ((ℚ_[p])ˣ ⧸ (powMonoidHom p : (ℚ_[p])ˣ →* (ℚ_[p])ˣ).range) = p ^ 2 := by sorry
