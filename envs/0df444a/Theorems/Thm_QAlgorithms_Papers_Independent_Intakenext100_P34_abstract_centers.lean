-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_abstract_centers
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.abstract_centers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:04:00.185102+00:00
-- url     : https://prove2.me/theorems/b6f94967-65eb-4dc5-9a88-c1505f838876
-- title:
--   The two BMW centers are cancellation rings
-- statement:
--   Let $C$ be a commutative unital ring in which $2$ is invertible, let $\epsilon\in\{1,-1\}$, and fix scalars $z_0^{(\ell)}\in C$ for all $\ell\ge0$. Write $\mathcal W_k$ for the actual quotient defined by (2.1)–(2.5) and (2.21)–(2.24), and $z_0(u)=\sum_{\ell\ge0}z_0^{(\ell)}u^{-\ell}$.
--
--   For the center statements, specialize $\kappa_0,\kappa_1$ to scalars and assume the identity
--   $$
--   (z_0(-u)-\tfrac12-\epsilon u)(z_0(u)-\tfrac12+\epsilon u)=(\tfrac12-\epsilon u)(\tfrac12+\epsilon u).
--   $$
--
--   Let $D$ be a commutative unital ring, with units $q,z,Q=q-q^{-1}$ and scalars $Z_0^{(\ell)}\in D$ for every integer $\ell$. Assume $Z_0^{(0)}=1+(z-z^{-1})/Q$. Write $W_k$ for the quotient of the affine braid group algebra by (2.42)–(2.43), with $Y_1=zX^{\epsilon_1}$, $Y_{i+1}=T_iY_iT_i$, and $E_i=1-(T_i-T_i^{-1})/Q$. Both left and right versions of its defining relations are imposed.
--
--   For the center statements assume the scalar formal-series identity
--   $$
--   \left(Z_0^- -\frac zQ-\frac{u^2}{u^2-1}\right)
--   \left(Z_0^+ +\frac{z^{-1}}Q-\frac{u^2}{u^2-1}\right)
--   =-\frac{(u^2-q^2)(u^2-q^{-2})}{Q^2(u^2-1)^2},
--   $$
--   where $Z_0^\pm=\sum_{\ell\ge0}Z_0^{(\pm\ell)}u^{-\ell}$.
--
--   For positive levels, the canonical polynomial and Laurent evaluations are injective and identify the two centers as
--   $$
--   Z(\mathcal W_k)=\{f\in C[y_1,\ldots,y_k]^{S_k}:f(y_1,-y_1,y_3,\ldots)=f(0,0,y_3,\ldots)\},
--   $$
--   $$
--   Z(W_l)=\{f\in D[Y_1^{\pm1},\ldots,Y_l^{\pm1}]^{S_l}:f(Y_1,Y_1^{-1},Y_3,\ldots)=f(1,1,Y_3,\ldots)\}.
--   $$
--   The affine coefficient ring $D$ and its parameters can be chosen independently of the degenerate coefficient ring $C$. At level one there is no pair substitution and the entire polynomial or Laurent polynomial algebra is the center.
--
--   These are the precise two center identifications asserted in the abstract; no assertion about quantum algorithms or the expected generators (4.32) is included.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 1, Abstract main result

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Abstract main result, PDF p.1, precisely the conjunction of the two
center identifications (Theorems 4.2 and 4.5, pp.20--25). The two
coefficient rings and parameter systems are independent. -/
theorem abstract_centers (P : DParams C) (k : ℕ) (hk : 0 < k)
    (hscalar : P.scalarKappa.isSome) (hd : DAdmissible C P)
    (D : Type u) [CommRing D] (Q : AParams D) (l : ℕ) (hl : 0 < l)
    (ha : AAdmissible D Q) :
    DCenterDescription C P k ∧ ACenterDescription D Q l := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
