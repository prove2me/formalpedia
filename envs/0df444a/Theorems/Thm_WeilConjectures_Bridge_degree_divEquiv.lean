-- Prove2me | Theorems.Thm_WeilConjectures_Bridge_degree_divEquiv
-- name    : WeilConjectures.Bridge.degree_divEquiv
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:23:49.048242+00:00
-- url     : https://prove2.me/theorems/dabd0dc2-7698-4914-bf42-44364d2cc653
-- title:
--   The divisor dictionary between the Riemann–Roch library and FLT preserves degrees
-- statement:
--   Let $k\subseteq K$ be an arbitrary field extension. Two formalizations of the places of $K/k$ are compared:
--
--   1. the places $P$ of the Riemann–Roch library: valuation rings $\mathcal O_P$ with $k\subseteq\mathcal O_P\subsetneq K$ whose value group is (order-)isomorphic to $\mathbb Z$;
--   2. the places $v$ of the FLT project: valuation rings $\mathcal O_v$ with $k\subseteq\mathcal O_v\subsetneq K$ that are principal ideal rings, i.e. discrete valuation rings.
--
--   The map $P\mapsto\pi(P)$ keeping the same valuation ring is a bijection between them. A divisor is, on either side, a finitely supported function from places to $\mathbb Z$, and $\Phi$ denotes the reindexing of divisors along $\pi$: $\Phi(D)(\pi(P))=D(P)$. On both sides the degree of a place is the dimension over $k$ of the residue field $\kappa(P)=\mathcal O_P/\mathfrak m_P$, and the degree of a divisor is $\deg D=\sum_P D(P)\,[\kappa(P):k]$.
--
--   Then for every divisor $D$ of the Riemann–Roch library,
--   $$\deg^{\mathrm{FLT}}\big(\Phi(D)\big)=\deg(D).$$
--
--   Together with the corresponding statement for $\ell(D)$, this lets results about divisors proved in one framework be used in the other, in particular the Riemann–Roch theorem in the FLT framework.
--
--   **Formalization Note** The places are `FunctionField.Place k K` and `AlgebraicCurve.Place k K`, the divisor equivalence is `WeilConjectures.Bridge.divEquiv k K = Finsupp.domCongr (placeEquiv k K)`. Dimensions (degrees of places, $\ell$) are `Module.finrank` over $k$, which is $0$ for an infinite-dimensional space; with this convention no hypothesis beyond `Algebra k K` is needed. The degree on the FLT side is `AlgebraicCurve.Divisor.degree`, on the library side `FunctionField.Divisor.deg k K`.
-- source:
--   Comparison lemma between two formalizations of divisors; no counterpart in the literature (the notion is the degree of a divisor, H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.4). Lean: bridge written for this port, file `Bridge/RiemannRochFLT.lean`

import Mathlib
import Definitions.Def_WeilConjectures_RiemannRochFLT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped WithZero
open MonoidWithZeroHom
open WeilConjectures.Bridge
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}

theorem WeilConjectures.Bridge.degree_divEquiv (D : FunctionField.Divisor k K) :
    AlgebraicCurve.Divisor.degree (divEquiv k K D) = FunctionField.Divisor.deg k K D := by sorry
