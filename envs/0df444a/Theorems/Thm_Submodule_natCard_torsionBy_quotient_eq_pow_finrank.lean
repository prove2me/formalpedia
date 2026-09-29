-- Prove2me | Theorems.Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank
-- name    : Submodule.natCard_torsionBy_quotient_eq_pow_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/b1dbb98d-aadb-518e-aab4-fcd7ed974053
-- title:
--   Torsion of a quotient by a lattice: #(V/L)[n]=n^{rk L}
-- statement:
--   Let $K$ be a division ring of characteristic $0$, and let $V$ be an additive commutative group equipped with a $K$-module structure. Let $L$ be a $\mathbb{Z}$-submodule of $V$ which, as a $\mathbb{Z}$-module, is free and finitely generated (no discreteness is assumed, and $L$ need not span $V$), and let $n$ be a natural number with $n \neq 0$. The assertion is an equality of natural numbers: the cardinality, in the sense of `Nat.card`, of the $n$-torsion submodule $\mathrm{torsionBy}\,\mathbb{Z}\,(V/L)\,(n)$ — that is, of the subgroup of those classes $x$ in the quotient $\mathbb{Z}$-module $V \,⧸\, L$ with $n \cdot x = 0$ — equals $n^{r}$, where $r = \mathrm{finrank}_{\mathbb{Z}} L$ is the $\mathbb{Z}$-rank of $L$. In particular the torsion subgroup is finite, since a `Nat.card` equal to the nonzero number $n^{r}$ forces finiteness. The $K$-module structure on $V$ enters only through the requirement that $V$ be uniquely divisible enough for division by $n$, and $K$ itself does not appear in the conclusion.
--
--   This is the purely algebraic, lattice-counting half of the classical torsion count $\#A[n] = n^{2g}$ for a complex torus $A = \mathbb{C}^{g}/\Lambda$. It is applied with $V$ a complex vector space of holomorphic differentials or their dual and $L$ a period lattice, and is used for torsion counts on Jacobians and on degree-zero Picard groups of complex curves, as well as in a bound relating quotient cardinalities to cardinalities of torsion subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Submodule.natCard_torsionBy_quotient_eq_pow_finrank
    {K : Type*} [DivisionRing K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L := by sorry
