-- Prove2me | Theorems.Thm_WeierstrassCurve_rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq
-- name    : WeierstrassCurve.rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/bf45cedc-c1c3-599a-af50-3dfdbdd0a665
-- title:
--   Root multiplicities of Φ_N(j(E),Y) count cyclic N-subgroups
-- statement:
--   Fix $N \geq 1$ (a natural number with `NeZero N`) together with a datum `data : ModularPolynomialData N`, that is a polynomial $\Phi =$ `data.Φ` in $\mathbb{Z}[X][Y]$ which is monic in $Y$, whose $Y$-degree equals $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies $\Phi(j(q), j(q^N)) = 0$ after substituting the Laurent $q$-expansions of $j$ and $j(q^N)$ via `evalAtJ` and `jqN`. Let $L$ be an algebraically closed field with decidable equality in which the image of $N$ is nonzero, let $E$ be a Weierstrass curve over $L$ which is elliptic, and let $y \in L$. Form the polynomial $\Phi(j(E), Y) \in L[Y]$ by mapping each coefficient of $\Phi$ (a polynomial over $\mathbb{Z}$) to $L$ through evaluation at the $j$-invariant $E.j$ along $\mathbb{Z} \to L$. The assertion is that the multiplicity of $y$ as a root of $\Phi(j(E), Y)$ equals the cardinality (as a `Nat.card`) of the type of subgroups $H$ of the group of affine points $E$ that are additively cyclic with $\mathrm{card}(H) = N$ and satisfy $E.\mathrm{cyclicQuotientJ}\,H\,N = y$, where the latter quantity is $c_4^3/\Delta$ of the Weierstrass curve obtained from $E$ and $H$ by the iteration `cqjIterate`.
--
--   This is the multiplicity-counted form of the classical statement that $\Phi_N(j(E), Y) = \prod_H (Y - j(E/H))$, the product running over the cyclic subgroups of order $N$ of an elliptic curve $E$ over an algebraically closed field of characteristic prime to $N$; multiple roots thus record coincidences $j(E/H) = j(E/H')$ for distinct $H$. It supports the separability statement for $\Phi_N(j(E),Y)$ at transcendental $j$, the characterisation of the roots of $\Phi_N(j(E),Y)$ in terms of quotient $j$-invariants, and the descent of $j(E/H)$ into the image of a base-change map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve

universe u in

theorem WeierstrassCurve.rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq
    (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (L : Type u) [Field L] [DecidableEq L] [IsAlgClosed L] (hN : (N : L) ≠ 0)
    (E : WeierstrassCurve L) [E.IsElliptic] (y : L) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j)).rootMultiplicity y =
      Nat.card {H : AddSubgroup E.toAffine.Point //
        (IsAddCyclic H ∧ Nat.card H = N) ∧ E.cyclicQuotientJ H N = y} := by sorry
