-- Prove2me | Theorems.Thm_WeierstrassCurve_isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet
-- name    : WeierstrassCurve.isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/2cf0e742-3aed-5063-949f-168010cd5c4a
-- title:
--   Supersingular j-invariant forces formal height two
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $k$ be a field of characteristic $q$, and let $W$ be a Weierstrass curve over $k$ that is elliptic (its discriminant is a unit). Let $\Omega$ be an algebraically closed field of characteristic $q$ and $\iota : k \to \Omega$ a ring homomorphism such that $\iota(j(W))$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is: every elliptic Weierstrass curve $W'$ over $\Omega$ with $j(W') = \iota(j(W))$ has the property that any point $P$ of its affine model with $q \cdot P = 0$ is the zero point. Let $F$ be a formal group over $k$ whose underlying two-variable power series is $W$'s normalised Weierstrass formal group law `W.formalGroupLawFixed`, obtained by substituting `W.fgZ3Fixed` into the formal inverse series `W.fgInv`. The conclusion is `F.IsDrinfeldBasisAdic ⊥ q 0 0`: reading the adic structure on $k$ with respect to the zero ideal, there is a unit power series $u \in k\langle\!\langle X \rangle\!\rangle$ with `F.nthSeries q` $= u \cdot$ `F.drinfeldDivisor q 0 0`, so that $(0,0)$ is a Drinfeld basis of level $q$ for $F$; by the cited criterion this amounts to `F.nthSeries q` $= u \cdot X^{q^2}$, i.e. $F$ has height two.
--
--   This is the Deuring-type statement that a supersingular $j$-invariant (here in the form of vanishing $q$-torsion for all $\Omega$-models with that $j$-invariant) forces the formal group of the Weierstrass curve to have height two, equivalently that the pair $(0,0)$ is a Drinfeld basis of level $q$. It feeds the construction of Drinfeld-basis data over completed local rings at supersingular points used in the level-moduli packages, and a variant of it phrased with an explicit primality hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (k : Type) [Field k] [CharP k q]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (ι : k →+* Ω) (hss : ι W.j ∈ ModularCurve.ssJSet q Ω)
    (F : FormalGroup k) (hF : F.toPowerSeries = W.formalGroupLawFixed) :
    F.IsDrinfeldBasisAdic ⊥ q 0 0 := by sorry
