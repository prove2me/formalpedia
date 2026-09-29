-- Prove2me | Theorems.Thm_WeierstrassCurve_prePsi_ne_zero_of_isElliptic
-- name    : WeierstrassCurve.prePsi_ne_zero_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/1f34ef13-d011-560a-a98c-cd8598b11215
-- title:
--   Odd division polynomials of an elliptic curve are non-zero
-- statement:
--   Let $K$ be a field and let $W$ be a Weierstrass curve over $K$ which is elliptic, i.e. carries the typeclass assumption that its discriminant $\Delta$ is a unit in $K$. Let $n$ be a natural number and assume $n$ is odd. The conclusion is that the polynomial $W.\mathrm{pre}\Psi'\,n \in K[X]$ — Mathlib's normalised division polynomial indexed by the natural numbers, which for odd $n$ is the $n$-th division polynomial $\psi_n$ itself — is not the zero polynomial. No assumption is made on the characteristic of $K$ or on the residue of $n$ modulo that characteristic; in particular the case where the characteristic is an odd prime $p$ dividing $n$, so that the classical leading coefficient $n$ of $\psi_n$ vanishes and the degree drops, is included. The statement is phrased entirely in terms of Mathlib's `WeierstrassCurve` API.
--
--   This is the non-vanishing of the odd division polynomials $\psi_n$ of an elliptic curve over an arbitrary field, the substance being the case where the characteristic divides $n$ (for instance $n=p$ in characteristic $p$), where the leading term degenerates. It is used in the identification of the relevant coefficient of $\mathrm{pre}\Psi$ with the Hasse invariant and in the analysis of the associated power series in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_prePsi_ne_zero_of_isElliptic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve

theorem WeierstrassCurve.prePsi_ne_zero_of_isElliptic {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : Odd n) : W.preΨ' n ≠ 0 := by sorry
