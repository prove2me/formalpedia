-- Prove2me | Theorems.Thm_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ
-- name    : WeierstrassCurve.map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/1bbf4963-df01-5f70-9d81-c59e6925b40d
-- title:
--   Splitting of the modular polynomial at every elliptic curve
-- statement:
--   Fix an integer $N \ge 1$ and a datum `data : ModularPolynomialData N`, that is: a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, whose degree in $Y$ equals $\mathrm{dedekindPsi}\,N = \sum_{d \mid N,\ d\ \text{squarefree}} N/d$, and which satisfies $\Phi\bigl(\,\cdot\,\bigr) = 0$ after substituting for the coefficient variable $X$ the $q$-expansion `jq` of the modular invariant (via the ring homomorphism `evalAtJ` into Laurent series over $\mathbb{Q}$) and for $Y$ the series `jqN N`, i.e. the expansion of $j(q^N)$. Let $L$ be an algebraically closed field in which $N \ne 0$, and let $E$ be a Weierstrass curve over $L$ which is elliptic. The assertion is an identity in $L[Y]$: the polynomial obtained from $\Phi$ by applying to each coefficient the evaluation $\mathbb{Z}[X] \to L$, $X \mapsto E.j$, equals the (finitely supported) product, over all additive subgroups $H$ of the group of affine points of $E$ over $L$ that are cyclic and satisfy $\mathrm{card}\,H = N$, of $Y - E.\mathrm{cyclicQuotientJ}\,H\,N$, where the latter element of $L$ is $c_4^3/\Delta$ of the Weierstrass curve `E.cyclicQuotientCurve H N` produced by the iterated quotient construction along $H$.
--
--   This is Kronecker's relation in the form of Lang's splitting of the level-$N$ modular polynomial at an arbitrary elliptic curve over an algebraically closed field of characteristic prime to $N$: the roots of $\Phi_N(j(E),Y)$, with multiplicity, are exactly the invariants $j(E/H)$ for the cyclic subgroups $H \subseteq E(L)$ of order $N$. It is used to compute the multiplicity of a given value among these invariants, in [`WeierstrassCurve.rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq`](thm.html#WeierstrassCurve.rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve

universe u in

theorem WeierstrassCurve.map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ
    (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (L : Type u) [Field L] [DecidableEq L] [IsAlgClosed L] (hN : (N : L) ≠ 0)
    (E : WeierstrassCurve L) [E.IsElliptic] :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j) =
      ∏ᶠ H ∈ {H : AddSubgroup E.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N},
        (Polynomial.X - Polynomial.C (E.cyclicQuotientJ H N)) := by sorry
