-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_theorem4_5
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.theorem4_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:09:28.851376+00:00
-- url     : https://prove2.me/theorems/27535ef6-807d-4b38-8915-c59263edf7ff
-- title:
--   The affine BMW center
-- statement:
--   Let $C$ be a commutative unital ring, with units $q,z,Q=q-q^{-1}$ and scalars $Z_0^{(\ell)}\in C$ for every integer $\ell$. Assume $Z_0^{(0)}=1+(z-z^{-1})/Q$. Write $W_k$ for the quotient of the affine braid group algebra by (2.42)–(2.43), with $Y_1=zX^{\epsilon_1}$, $Y_{i+1}=T_iY_iT_i$, and $E_i=1-(T_i-T_i^{-1})/Q$. Both left and right versions of its defining relations are imposed.
--
--   For the center statements assume the scalar formal-series identity
--   $$
--   \left(Z_0^- -\frac zQ-\frac{u^2}{u^2-1}\right)
--   \left(Z_0^+ +\frac{z^{-1}}Q-\frac{u^2}{u^2-1}\right)
--   =-\frac{(u^2-q^2)(u^2-q^{-2})}{Q^2(u^2-1)^2},
--   $$
--   where $Z_0^\pm=\sum_{\ell\ge0}Z_0^{(\pm\ell)}u^{-\ell}$.
--
--   For $k\ge1$, Laurent evaluation $\operatorname{ev}_Y:C[Y_1^{\pm1},\ldots,Y_k^{\pm1}]\to W_k$ is injective and
--   $$
--   Z(W_k)=\operatorname{ev}_Y\{f\in C[Y_1^{\pm1},\ldots,Y_k^{\pm1}]^{S_k}:
--    f(Y_1,Y_1^{-1},Y_3,\ldots,Y_k)=f(1,1,Y_3,\ldots,Y_k)\}.
--   $$
--   The Laurent ring has finite support in integer exponent vectors, and its substitution maps are formal. At level one no pair test is imposed and the center is the whole Laurent polynomial algebra.
--
--   The conclusion identifies the center of the unrestricted affine algebra. The conjectural generator description (4.32) is excluded.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 24, Theorem 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Theorem 4.5, PDF pp.24--25. The hypotheses of the basis theorem
used by its first proof step are retained; (4.32) is not asserted. -/
theorem theorem4_5 (P : AParams C) (k : ℕ) (hk : 0 < k) (hadm : AAdmissible C P) :
    ACenterDescription C P k := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
