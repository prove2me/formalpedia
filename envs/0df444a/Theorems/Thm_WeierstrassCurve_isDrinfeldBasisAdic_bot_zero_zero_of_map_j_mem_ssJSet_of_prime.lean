-- Prove2me | Theorems.Thm_WeierstrassCurve_isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet_of_prime
-- name    : WeierstrassCurve.isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/8451be8d-78b8-511f-99ec-0acb7989b7fd
-- title:
--   Supersingular j-invariant forces formal height two
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $W$ a Weierstrass curve over $k$ which is elliptic. Let $\Omega$ be an algebraically closed field of characteristic $q$ and $\iota : k \to \Omega$ a ring homomorphism, and assume $\iota(j(W))$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is: every elliptic Weierstrass curve $W'$ over $\Omega$ with $j(W') = \iota(j(W))$ has the property that an affine point $P$ of $W'$ with $q \cdot P = 0$ must be $0$. Let $F$ be a formal group over $k$ whose underlying two-variable power series is $W$'s Weierstrass formal group law `W.formalGroupLawFixed`, obtained by substituting `W.fgZ3Fixed` into the formal inverse series `W.fgInv`. The conclusion is `F.IsDrinfeldBasisAdic ⊥ q 0 0`: taking the zero ideal of $k$ as the defining ideal, $(0,0)$ is a Drinfeld basis of level $q$ for $F$, i.e. there is a unit power series $u$ over $k$ with $F.\mathrm{nthSeries}\,q = u \cdot F.\mathrm{drinfeldDivisor}\,q\,0\,0$; by [`FormalGroup.isDrinfeldBasisAdic_zero_zero_iff`](thm.html#FormalGroup.isDrinfeldBasisAdic_zero_zero_iff) this says that the multiplication-by-$q$ series of $F$ is a unit times $Z^{q^2}$.
--
--   This is the classical statement that an elliptic curve with supersingular $j$-invariant has formal group of height two, so that $[q]_F(Z) = u\,Z^{q^2}$ with $u$ a unit; it holds for every prime, removing the restriction $q \neq 2$ present in [`WeierstrassCurve.isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet`](thm.html#WeierstrassCurve.isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet). It feeds the construction of the local moduli rings with Drinfeld level structure at a supersingular point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet_of_prime.lean

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

theorem WeierstrassCurve.isDrinfeldBasisAdic_bot_zero_zero_of_map_j_mem_ssJSet_of_prime
    (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [CharP k q]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (ι : k →+* Ω) (hss : ι W.j ∈ ModularCurve.ssJSet q Ω)
    (F : FormalGroup k) (hF : F.toPowerSeries = W.formalGroupLawFixed) :
    F.IsDrinfeldBasisAdic ⊥ q 0 0 := by sorry
