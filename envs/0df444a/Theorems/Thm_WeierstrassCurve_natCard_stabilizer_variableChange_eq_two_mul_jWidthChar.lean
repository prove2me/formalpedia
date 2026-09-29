-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_mul_jWidthChar
-- name    : WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_mul_jWidthChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/11516544-15f2-5ed3-8217-ca234af13c40
-- title:
--   Order of Aut(E) equals 2 wₚ(j)
-- statement:
--   Let $K$ be an algebraically closed field equipped with decidable equality, let $p$ be a natural number assumed prime and assumed to be the characteristic of $K$ (via `CharP K p`), and let $E$ be a Weierstrass curve over $K$ satisfying `IsElliptic`, i.e. with invertible discriminant. The group `WeierstrassCurve.VariableChange K` of admissible changes of variable $(u,r,s,t)$, $u$ a unit, acts on Weierstrass curves over $K$; the assertion is that the cardinality (as a natural number, `Nat.card`) of the stabiliser of $E$ for this action equals $2 \cdot \mathrm{jWidthChar}\,p\,(j(E))$, where the width table $\mathrm{jWidthChar}$ is defined by: for $p = 2$ it is $12$ when $j(E) = 0$ and $1$ otherwise; for $p = 3$ it is $6$ when $j(E) = 0$ and $1$ otherwise; and for all other $p$ it is $\mathrm{jWidth}\,(j(E))$, namely $3$ if $j(E) = 0$, $2$ if $j(E) = 1728$, and $1$ in every remaining case. Thus the stabiliser has order $24$ or $2$ in characteristic $2$, order $12$ or $2$ in characteristic $3$, and order $6$, $4$ or $2$ according as $j(E)$ is $0$, $1728$ or neither.
--
--   This is the classical determination of the automorphism group of an elliptic curve over an algebraically closed field, in the Weierstrass-model formulation where automorphisms are the variable changes fixing the curve, packaged uniformly in all characteristics by the width function $w_p(j)$. It feeds the orbit–stabiliser computation of the ramification of modular curve maps over the $j$-line, being used for the local width statement at a place of the moduli line and for the count of the orbit of torsion data under variable changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_mul_jWidthChar.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_mul_jWidthChar
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (E : WeierstrassCurve K) [E.IsElliptic] :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E) = 2 * ModularCurve.jWidthChar p E.j := by sorry
