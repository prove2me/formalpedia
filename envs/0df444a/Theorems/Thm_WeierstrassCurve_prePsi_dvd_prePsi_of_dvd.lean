-- Prove2me | Theorems.Thm_WeierstrassCurve_prePsi_dvd_prePsi_of_dvd
-- name    : WeierstrassCurve.prePsi_dvd_prePsi_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/8e530820-3a8b-5658-b61b-5719f845c344
-- title:
--   Division polynomials form a divisibility sequence
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$. For an integer $n$, $W.\mathrm{pre\Psi}\ n$ denotes Mathlib's univariate division polynomial of $W$ in $R[X]$, the normalised elliptic divisibility sequence attached to $W$ whose relation to the usual division polynomials is $\psi_n = W.\mathrm{pre\Psi}\ n$ for $n$ odd and $\psi_n = W.\mathrm{pre\Psi}\ n\cdot\psi_2$ for $n$ even, with $\psi_2 = 2y + a_1x + a_3$; in particular $\mathrm{pre\Psi}\ 0 = 0$ and $\mathrm{pre\Psi}\ 1 = \mathrm{pre\Psi}\ 2 = 1$. The assertion is that for all integers $m$ and $n$ with $m \mid n$ in $\mathbb{Z}$, one has $W.\mathrm{pre\Psi}\ m \mid W.\mathrm{pre\Psi}\ n$ in the polynomial ring $R[X]$. No hypothesis on $R$ beyond commutativity is imposed, the indices range over all of $\mathbb{Z}$ (both signs, and the degenerate case $m = 0$, where $n = 0$ as well), and no non-degeneracy or invertibility assumption on the coefficients of $W$ is required. The proof cites [`isEllSequence_normEDS`](thm.html#isEllSequence_normEDS), which states that for elements $b, c, d$ of a commutative ring the normalised sequence `normEDS b c d` satisfies the predicate [`IsEllSequence'`](def/Compat_Mathlib430.html#L237).
--
--   This is the classical statement that the division polynomials of a Weierstrass curve form a divisibility sequence, i.e. $\psi_m \mid \psi_n$ whenever $m \mid n$, in the form of Ward's theorem that an elliptic divisibility sequence is a divisibility sequence. It is used in the study of kernels of isogenies and cyclic torsion subschemes, for instance in the factorisation of division polynomials over a cyclic generic kernel and in the associated statements about $\Gamma_0$-structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_prePsi_dvd_prePsi_of_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Polynomial

theorem WeierstrassCurve.prePsi_dvd_prePsi_of_dvd
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) {m n : ℤ} (hmn : m ∣ n) :
    W.preΨ m ∣ W.preΨ n := by sorry
