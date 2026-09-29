-- Prove2me | Theorems.Thm_W54_pow_smul_tateModule_eq_vanishing
-- name    : W54.pow_smul_tateModule_eq_vanishing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/c1b4cb2d-2aae-5cad-ab4b-efb0b84652f3
-- title:
--   pⁿ-divisibility in the Tate module detects vanishing at n
-- statement:
--   Let $p$ be a natural number and let $J$ be an additive commutative group equipped with a module structure over the abstract Hecke algebra `HeckeAlg`, that is, over the polynomial ring $\mathbb{Z}[T_\ell : \ell \text{ prime}]$ in indeterminates indexed by the primes. Recall that [`TateModule p J`](def/EllipticCurve_TateModule.html#L15) is the `HeckeAlg`-submodule of the sequence module $\mathbb{N} \to J$ consisting of those $x$ with $x_0 = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$. Fix $n : \mathbb{N}$ and a sequence $x : \mathbb{N} \to J$ lying in [`TateModule p J`](def/EllipticCurve_TateModule.html#L15). The assertion is the equivalence of the following two statements: there exists $y$ in [`TateModule p J`](def/EllipticCurve_TateModule.html#L15) with $p^n \cdot y = x$ (scalar multiplication by the natural number $p^n$ in the sequence module); and $x_n = 0$. No primality assumption is placed on $p$, and no divisibility, torsion or completeness hypothesis on $J$ is required.
--
--   This is the elementary structural fact that, in the Tate module realised as the module of sequences satisfying the transition relations $p\,x_{n+1} = x_n$ with $x_0 = 0$, the elements divisible by $p^n$ are exactly those vanishing in the $n$-th component, the divisor being obtainable inside the Tate module itself. It is used in the analysis of Hecke modules attached to modular curves, feeding into [`CuspForm.isFlatAt_of_point_of_not_dvd`](thm.html#CuspForm.isFlatAt_of_point_of_not_dvd) and [`RibetIrr.irreducible_of_point_of_not_dvd`](thm.html#RibetIrr.irreducible_of_point_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_W54_pow_smul_tateModule_eq_vanishing.lean

import Definitions.Def_ModularCurve_EichlerShimuraData
import Mathlib.NumberTheory.Padics.RingHoms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem W54.pow_smul_tateModule_eq_vanishing {p : ℕ} {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    (n : ℕ) {x : ℕ → J} (hx : x ∈ TateModule p J) :
    (∃ y ∈ TateModule p J, (p ^ n : ℕ) • y = x) ↔ x n = 0 := by sorry
