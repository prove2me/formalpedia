-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_auxiliary_function_nonvanishing
-- name    : WeierstrassEllipticZeta.auxiliary_function_nonvanishing
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T11:56:22.920985+00:00
-- url     : https://prove2.me/theorems/cf839c2d-4090-4fd7-b4d2-e032d895d6fb
-- title:
--   Functional nonvanishing of polynomials in z, wp and zeta
-- statement:
--   Let $L$ be any complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\zeta$. Let $m,\ell\ge0$ be integers. For every nonzero complex coefficient array $(c_{ijk})_{0\le i\le m,\ 0\le j,k\le\ell}$, there is a point $z\in\mathbb C\setminus\Lambda$ such that
--
--   $$\sum_{i=0}^{m}\sum_{j=0}^{\ell}\sum_{k=0}^{\ell}c_{ijk}z^i\wp(z)^j\zeta(z)^k\ne0.$$
--
--   Thus the rectangular family of monomials in $z,\wp(z),\zeta(z)$ is linearly independent over $\mathbb C$ as functions on the regular locus. There are no algebraicity conditions on the lattice invariants or coefficient-height restrictions. This is the polynomial nonvanishing form of functional algebraic independence used in the proof of Lemma 9. It does not give a bound on the location of a nonzero value or on any derivative order.
-- source:
--   Senthil Kumar K (2026), proof of Lemma 9, which invokes algebraic independence over C of the functions z, wp(z), and zeta(z), https://doi.org/10.1017/S001309152610145X. This is its rectangular finite-coefficient formulation on the regular locus. Functional independence remains a proof obligation.

import Definitions.Def_WeierstrassEllipticZeta_Defs

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.auxiliary_function_nonvanishing
    (L : PeriodPair) (m l : ℕ)
    (c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ)
    (hc : c ≠ 0) :
    ∃ z : ℂ, z ∉ L.lattice ∧
      (∑ i, c i * z ^ i.1.val * L.weierstrassP z ^ i.2.1.val *
        weierstrassZeta L z ^ i.2.2.val) ≠ 0 := by sorry
