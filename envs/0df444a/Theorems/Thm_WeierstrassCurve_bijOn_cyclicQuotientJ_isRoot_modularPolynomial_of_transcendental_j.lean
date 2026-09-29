-- Prove2me | Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
-- name    : WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/8a5d57b2-d946-56a5-8468-bac6c5c81cc7
-- title:
--   Cyclic N-subgroups biject with the roots of Φ_N(j(E),Y)
-- statement:
--   Let $K$ be a field and $N$ a nonzero natural number, and let `data` be a datum of level $N$ in the sense of `ModularPolynomialData N`: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ that is monic in $Y$, of degree $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ in $Y$, and satisfies $\Phi(j(q), j(q^N)) = 0$ after substituting the Laurent series $j(q)$ for the coefficient variable and $j(q^N)$ for $Y$. Let $L$ be an algebraically closed field that is a $K$-algebra, with $N \neq 0$ in $L$, and let $E$ be a Weierstrass curve over $L$ which is elliptic and whose $j$-invariant $j(E)$ is transcendental over $K$. For a subgroup $H$ of the group of affine points $E(L)$ and for $N$, write $E.\mathrm{cyclicQuotientJ}\,H\,N = c_4^3/\Delta$ of the curve obtained from $E$ and $H$ by the iterated Vélu construction `cyclicQuotientCurve`. Then $H \mapsto E.\mathrm{cyclicQuotientJ}\,H\,N$ is a bijection from the set of cyclic subgroups $H \le E(L)$ with $\operatorname{card} H = N$ onto the set of roots in $L$ of the one-variable polynomial obtained from $\Phi$ by evaluating each integer coefficient polynomial at $X = j(E)$: it maps the first set into the second, is injective on it, and its image is exactly the second set.
--
--   This is the explicit form of Kronecker's theorem on the modular equation, sharpened by Igusa: over an algebraically closed field of residue characteristic prime to $N$ and for a curve with transcendental $j$-invariant, the $\psi(N)$ roots of $\Phi_N(j(E), Y)$ are pairwise distinct and are precisely the $j$-invariants of the quotients of $E$ by its cyclic subgroups of order $N$. It underlies the separability of the fibre polynomial at a transcendental $j$ and the construction of the algebra homomorphisms from the modular function field sending $j(q^N)$ (and its divisor-level variants) to the quotient $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve

universe u v in

theorem WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
    (K : Type u) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (L : Type v) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra K L]
    (hN : (N : L) ≠ 0) (E : WeierstrassCurve L) [E.IsElliptic] (hE : Transcendental K E.j) :
    Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H N)
      {H | IsAddCyclic H ∧ Nat.card H = N}
      {y | (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j)).IsRoot y} := by sorry
