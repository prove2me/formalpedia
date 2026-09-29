-- Prove2me | Theorems.Thm_Submodule_finite_torsionBy_pow_of_finite_torsionBy
-- name    : Submodule.finite_torsionBy_pow_of_finite_torsionBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/845a5ccd-361b-57c7-b2ab-2a48f5ea9798
-- title:
--   Finite a-torsion implies finite a^k-torsion
-- statement:
--   Let $R$ be a commutative ring, let $M$ be an $R$-module (its additive group being a commutative group), and let $a \in R$. The hypothesis is that the submodule `Submodule.torsionBy R M a`, that is $M[a] = \{x \in M : a \cdot x = 0\}$, is finite as a type. The conclusion is that for every natural number $k$ the submodule `Submodule.torsionBy R M (a ^ k)`, namely $M[a^k] = \{x \in M : a^k \cdot x = 0\}$, is again finite. Note that $k$ is arbitrary, the case $k = 0$ giving the trivial submodule $\{0\}$; no hypotheses of Noetherianness, of finite generation, or on the nature of $a$ are imposed, and finiteness is asserted in the sense of the `Finite` typeclass on the coercion of the submodule to a type.
--
--   This is the elementary dévissage of a torsion module along the filtration by powers of $a$: finiteness of one torsion layer propagates to all layers. In this development it serves the finiteness statements for torsion in degree-zero divisor class groups of curves, being cited by [`AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero`](thm.html#AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero) and [`AlgebraicCurve.Pic0.finite_torsion_pow_char`](thm.html#AlgebraicCurve.Pic0.finite_torsion_pow_char).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_finite_torsionBy_pow_of_finite_torsionBy.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Submodule.finite_torsionBy_pow_of_finite_torsionBy
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R)
    (h : Finite (Submodule.torsionBy R M a)) (k : ℕ) :
    Finite (Submodule.torsionBy R M (a ^ k)) := by sorry
