-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_remark4_6
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.remark4_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:09:48.603121+00:00
-- url     : https://prove2.me/theorems/da044072-bcbb-4af2-8fac-c7951a7120a8
-- title:
--   The affine rank-two contraction ideal and its center action
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
--   Assume $C\ne0$ and work at level two. Then
--   $$
--   W_2E_1=C[Y_1^{\pm1}]E_1,\qquad
--   \{Y_1^nE_1:n\in\mathbb Z\}\text{ is linearly independent over }C.
--   $$
--   Every central element acts on the entire ideal as multiplication by a scalar from $C$, and
--   $$
--   W_2\text{ is not a finitely generated }Z(W_2)\text{-module}.
--   $$
--   The equality and independence display the infinite free module meant by the source's infinite-dimensional assertion. Negative powers use the actual inverse of the flagpole generator.
--
--   Generic irreducibility is separately deferred because the source does not specify its generic parameter locus.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 26, Remark 4.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Remark 4.6, PDF p.26: the Laurent ideal, its integer-indexed free
family, scalar center action and non-finite-generation conclusion.
Generic irreducibility needs a separately specified parameter locus; see the audit. -/
theorem remark4_6 [Nontrivial C] (P : AParams C) (hadm : AAdmissible C P) :
    let j : Adj 2 := ⟨0, by decide⟩
    let e := awMap C P 2 (affineContractionWord C P j)
    let y := awMap C P 2 (affineYWord C P (adjacentLeft j) false)
    let yi := awMap C P 2 (affineYWord C P (adjacentLeft j) true)
    leftMultiples e = {a | ∃ f : AddMonoidAlgebra C ℤ,
      a = (AddMonoidAlgebra.coeff f).sum (fun n s => algebraMap C (AW C P 2) s * signedPow y yi n)*e} ∧
    LinearIndependent C (fun n : ℤ => signedPow y yi n*e) ∧
    (∀ c : AW C P 2, Central c → ∃ s : C,
      ∀ a ∈ leftMultiples e, c*a = algebraMap C (AW C P 2) s*a) ∧
    ¬ Module.Finite (Subalgebra.center C (AW C P 2)) (AW C P 2) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
