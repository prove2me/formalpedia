-- Prove2me | Theorems.Thm_WeilConjectures_Bridge_ell_divEquiv
-- name    : WeilConjectures.Bridge.ell_divEquiv
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:24:37.086349+00:00
-- url     : https://prove2.me/theorems/89226efb-c679-44f0-930a-b54714766812
-- title:
--   The divisor dictionary between the Riemann–Roch library and FLT preserves $\ell(D)$
-- statement:
--   Let $k\subseteq K$ be an arbitrary field extension. Two formalizations of the places of $K/k$ are compared:
--
--   1. the places $P$ of the Riemann–Roch library: valuation rings $\mathcal O_P$ with $k\subseteq\mathcal O_P\subsetneq K$ whose value group is (order-)isomorphic to $\mathbb Z$;
--   2. the places $v$ of the FLT project: valuation rings $\mathcal O_v$ with $k\subseteq\mathcal O_v\subsetneq K$ that are principal ideal rings, i.e. discrete valuation rings.
--
--   The map $P\mapsto\pi(P)$ keeping the same valuation ring is a bijection between them. A divisor is, on either side, a finitely supported function from places to $\mathbb Z$, and $\Phi$ denotes the reindexing of divisors along $\pi$: $\Phi(D)(\pi(P))=D(P)$. On both sides the degree of a place is the dimension over $k$ of the residue field $\kappa(P)=\mathcal O_P/\mathfrak m_P$, and the degree of a divisor is $\deg D=\sum_P D(P)\,[\kappa(P):k]$.
--
--   For a divisor $D$ of the Riemann–Roch library, $\mathcal L(D)=\{f\in K:\ f=0\ \text{or}\ v_P(f)\ge -D(P)\ \text{for every place } P\}$ with $v_P$ the normalized valuation of $P$, and for an FLT divisor $E$, $\mathcal L^{\mathrm{FLT}}(E)=\{f\in K:\ f=0\ \text{or}\ v(f)\ge -E(v)\ \text{for every FLT place } v\}$ with $v$ the normalized valuation of the discrete valuation ring $\mathcal O_v$; put $\ell=\dim_k\mathcal L$ on each side. Then for every divisor $D$ of the Riemann–Roch library,
--   $$\ell^{\mathrm{FLT}}\big(\Phi(D)\big)=\ell(D).$$
--
--   Together with the preservation of degrees, this transports the Riemann–Roch theorem of the library to the FLT framework.
--
--   **Formalization Note** The places are `FunctionField.Place k K` and `AlgebraicCurve.Place k K`, the divisor equivalence is `WeilConjectures.Bridge.divEquiv k K = Finsupp.domCongr (placeEquiv k K)`. Dimensions (degrees of places, $\ell$) are `Module.finrank` over $k$, which is $0$ for an infinite-dimensional space; with this convention no hypothesis beyond `Algebra k K` is needed. Valuations are multiplicative with values in $\mathbb Z^{m0}$: the conditions read `w.valuation f ≤ exp (D w)` (library) and `v.adicValuation f ≤ exp (E v)` (FLT, `adicValuation` being the adic valuation of the maximal ideal of $\mathcal O_v$). The spaces are `FunctionField.RRspace k K D` and `AlgebraicCurve.LSpace`, and the dimensions `FunctionField.ell k K D` and `AlgebraicCurve.ell`.
-- source:
--   Comparison lemma between two formalizations of Riemann–Roch spaces; no counterpart in the literature (the notion is $\mathcal L(A)$ and $\ell(A)$, H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.4). Lean: bridge written for this port, file `Bridge/RiemannRochFLT.lean`

import Mathlib
import Definitions.Def_WeilConjectures_RiemannRochFLT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped WithZero
open MonoidWithZeroHom
open WeilConjectures.Bridge
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}

theorem WeilConjectures.Bridge.ell_divEquiv (D : FunctionField.Divisor k K) :
    AlgebraicCurve.ell (divEquiv k K D) = FunctionField.ell k K D := by sorry
