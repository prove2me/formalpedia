-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_theorem3_6
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.theorem3_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:07:00.937535+00:00
-- url     : https://prove2.me/theorems/1a87e889-a176-4fa6-9c85-45e7b1d1efef
-- title:
--   Canonical affine compression elements and their recursions
-- statement:
--   Let $C$ be a commutative unital ring, with units $q,z,Q=q-q^{-1}$ and scalars $Z_0^{(\ell)}\in C$ for every integer $\ell$. Assume $Z_0^{(0)}=1+(z-z^{-1})/Q$. Write $W_k$ for the quotient of the affine braid group algebra by (2.42)–(2.43), with $Y_1=zX^{\epsilon_1}$, $Y_{i+1}=T_iY_iT_i$, and $E_i=1-(T_i-T_i^{-1})/Q$. Both left and right versions of its defining relations are imposed.
--
--   There is a compatible family of central Laurent-polynomial representatives $Z_n^{(\ell)}\in W_n$ ($n\ge0$, $\ell\in\mathbb Z$), starting at the supplied scalars, with
--   $$
--   E_iY_i^\ell E_i=Z_{i-1}^{(\ell)}E_i.
--   $$
--   Define $Z_n^\pm(u)=\sum_{\ell\ge0}Z_n^{(\pm\ell)}u^{-\ell}$, so both have zeroth coefficient $Z_n^{(0)}$. Put $H=u^2/(u^2-1)$ and
--   $$
--   R(Y,u)=\frac{(u-Y)^2(u-q^{-2}Y^{-1})(u-q^2Y^{-1})}{(u-Y^{-1})^2(u-q^2Y)(u-q^{-2}Y)}.
--   $$
--   For $i\ge1$, the identity in level $i+1$ is
--   $$
--   (Z_{i-1}^- -z/Q-H)(Z_{i-1}^+ +z^{-1}/Q-H)E_i
--   =-\frac{(u^2-q^2)(u^2-q^{-2})}{Q^2(u^2-1)^2}E_i.
--   $$
--   In level $i+2$,
--   $$
--   (Z_i^+ +z^{-1}/Q-H)E_{i+1}=(Z_{i-1}^+ +z^{-1}/Q-H)R(Y_i,u)E_{i+1}.
--   $$
--   For $k\ge1$, in level $k+1$,
--   $$
--   (Z_{k-1}^+ +z^{-1}/Q-H)E_k=(Z_0^+ +z^{-1}/Q-H)\prod_{j=1}^{k-1}R(Y_j,u)E_k.
--   $$
--   The positive representatives are constructed coefficientwise from this product. At positive levels, the negative representatives are obtained from the first identity using the unit constant $z/Q$ of the positive factor; at level zero the prescribed bilateral scalars are retained. Compression remains a conclusion and is never cancelled.
--
--   This supplies both recursions and the bilateral moment interface without assuming admissibility or tower injectivity.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 17, Theorem 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Theorem 3.6, PDF pp.16--18: centrality and compression for the
constructed representatives, followed by (3.26)--(3.28). Both positive and
negative moments have the same zeroth term. The squared denominator in
(3.26) is retained, and both stale E_(i+1) in (3.28) are corrected to E_k
as forced by its induction. No admissibility hypothesis is imposed. -/
theorem theorem3_6 (P : AParams C) :
    (∀ (n : ℕ) (ell : ℤ), 0 < n → Central (aMomentAt C P n n ell (le_refl n))) ∧
    (∀ (n : ℕ) (ell : ℤ),
      let j : Adj (n+2) := ⟨n, by omega⟩
      let m := awMap C P (n+2)
      m (affineContractionWord C P j)*signedPow (m (affineYWord C P (adjacentLeft j) false))
        (m (affineYWord C P (adjacentLeft j) true)) ell*m (affineContractionWord C P j) =
        aMomentAt C P n (n+2) ell (by omega)*m (affineContractionWord C P j)) ∧
    (∀ n : ℕ,
      let j : Adj (n+2) := ⟨n, by omega⟩
      let c := algebraMap C (AW C P (n+2))
      let e := ps (awMap C P (n+2) (affineContractionWord C P j))
      let h := 1+pairResolvent (1 : AW C P (n+2))
      (aMomentSeries C P n (n+2) (by omega) true-ps (c ((P.z : C)*(↑P.Q⁻¹ : C)))-h)*
        (aMomentSeries C P n (n+2) (by omega) false+ps (c ((↑P.z⁻¹ : C)*(↑P.Q⁻¹ : C)))-h)*e =
        -(ps (c ((↑P.Q⁻¹ : C)^2))*aScalarFraction (c (P.q : C)) (c (↑P.q⁻¹ : C)))*e) ∧
    (∀ n : ℕ,
      let j : Adj (n+3) := ⟨n+1, by omega⟩
      let y : Fin (n+3) := ⟨n, by omega⟩
      let m := awMap C P (n+3)
      let c := algebraMap C (AW C P (n+3))
      let e := ps (m (affineContractionWord C P j))
      let offset := ps (c ((↑P.z⁻¹ : C)*(↑P.Q⁻¹ : C)))-(1+pairResolvent (1 : AW C P (n+3)))
      (aMomentSeries C P (n+1) (n+3) (by omega)+offset)*e =
        (aMomentSeries C P n (n+3) (by omega)+offset)*
        aRatio (c (P.q : C)) (c (↑P.q⁻¹ : C)) (m (affineYWord C P y false)) (m (affineYWord C P y true))*e) ∧
    (∀ (k : ℕ) (hk : 0 < k),
      let j : Adj (k+1) := ⟨k-1, by omega⟩
      let m := awMap C P (k+1)
      let c := algebraMap C (AW C P (k+1))
      let e := ps (m (affineContractionWord C P j))
      let offset := ps (c ((↑P.z⁻¹ : C)*(↑P.Q⁻¹ : C)))-(1+pairResolvent (1 : AW C P (k+1)))
      (aMomentSeries C P (k-1) (k+1) (by omega)+offset)*e =
        (aMomentSeries C P 0 (k+1) (by omega)+offset)*
        (List.ofFn (fun a : Fin (k-1) =>
          let y : Fin (k+1) := ⟨a.val, by have := a.isLt; omega⟩
          aRatio (c (P.q : C)) (c (↑P.q⁻¹ : C)) (m (affineYWord C P y false)) (m (affineYWord C P y true)))).prod*e) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
