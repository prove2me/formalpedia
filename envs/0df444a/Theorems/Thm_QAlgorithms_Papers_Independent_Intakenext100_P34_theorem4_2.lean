-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_theorem4_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.theorem4_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:07:47.50199+00:00
-- url     : https://prove2.me/theorems/5f07dadd-ea13-42d3-a543-e0c0d203c9eb
-- title:
--   The degenerate affine BMW center
-- statement:
--   Let $C$ be a commutative unital ring in which $2$ is invertible, let $\epsilon\in\{1,-1\}$, and fix scalars $z_0^{(\ell)}\in C$ for all $\ell\ge0$. Write $\mathcal W_k$ for the actual quotient defined by (2.1)–(2.5) and (2.21)–(2.24), and $z_0(u)=\sum_{\ell\ge0}z_0^{(\ell)}u^{-\ell}$.
--
--   For the center statements, specialize $\kappa_0,\kappa_1$ to scalars and assume the identity
--   $$
--   (z_0(-u)-\tfrac12-\epsilon u)(z_0(u)-\tfrac12+\epsilon u)=(\tfrac12-\epsilon u)(\tfrac12+\epsilon u).
--   $$
--
--   For $k\ge1$, polynomial evaluation $\operatorname{ev}_y:C[y_1,\ldots,y_k]\to\mathcal W_k$ is injective, and
--   $$
--   Z(\mathcal W_k)=\operatorname{ev}_y\{f\in C[y_1,\ldots,y_k]^{S_k}:f(y_1,-y_1,y_3,\ldots,y_k)=f(0,0,y_3,\ldots,y_k)\}.
--   $$
--   The symmetry and substitution conditions are identities of formal polynomials over $C$. When $k=1$, the substitution condition is empty and the center is the full one-variable polynomial algebra.
--
--   This identifies the center as a particular subring of the presented algebra, rather than an unrelated abstract ring.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 20, Theorem 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Theorem 4.2, PDF pp.20--21. Scalar kappa specialization and (4.5)
are carried from the basis theorem invoked by the first proof step. -/
theorem theorem4_2 (P : DParams C) (k : ℕ) (hk : 0 < k)
    (hscalar : P.scalarKappa.isSome) (hadm : DAdmissible C P) :
    DCenterDescription C P k := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
