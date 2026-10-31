-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_proposition3_5
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.proposition3_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:06:17.740626+00:00
-- url     : https://prove2.me/theorems/f6603a40-52d0-428f-9fc6-720452e027c9
-- title:
--   Affine intertwiner identities
-- statement:
--   Let $C$ be a commutative unital ring, with units $q,z,Q=q-q^{-1}$ and scalars $Z_0^{(\ell)}\in C$ for every integer $\ell$. Assume $Z_0^{(0)}=1+(z-z^{-1})/Q$. Write $W_k$ for the quotient of the affine braid group algebra by (2.42)–(2.43), with $Y_1=zX^{\epsilon_1}$, $Y_{i+1}=T_iY_iT_i$, and $E_i=1-(T_i-T_i^{-1})/Q$. Both left and right versions of its defining relations are imposed.
--
--   Fix $i\ge1$ in level $i+1$ and write $v=Y_i/(u-Y_i)$, $w=Y_{i+1}/(u-Y_{i+1})$, $g=Y_iY_{i+1}/(u^2-Y_iY_{i+1})$, $t=T_i$, $t^{-1}=T_i^{-1}$, and $e=E_i$. Fractions are formal expansions at infinity. Then
--   $$
--   (ew-t/Q-g)(ev+t^{-1}/Q-g)
--   =-\frac1{Q^2}\bigl(1+(2-q^2-q^{-2})(g+g^2)\bigr),
--   $$
--   $$
--   (w+t/Q-eg)-Q^2(v+1)(w+t/Q-eg)v
--   =(tvt^{-1}+t/Q-eg)-Q^2w(eve+ze/Q-eg)(w+1).
--   $$
--   The first right-hand side equals the displayed fraction in (3.18), with its squared denominator. Every product appears in the source's order and the second factor in the first identity contains $T_i^{-1}$.
--
--   These are identities in the unrestricted affine quotient and require no admissibility hypothesis.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 15, Proposition 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Proposition 3.5, PDF pp.15--16, including both (3.18) and (3.19).
The RHS of (3.18) is written -Q⁻²(1+(2-q²-q⁻²)(g+g²)),
where g=Y_iY_(i+1)/(u²-Y_iY_(i+1)); this is the same formal fraction. -/
theorem proposition3_5 (P : AParams C) (i : ℕ) (hi : 1 ≤ i) :
    let j : Adj (i+1) := ⟨i-1, by omega⟩
    let m := awMap C P (i+1)
    let a := m (affineYWord C P (adjacentLeft j))
    let b := m (affineYWord C P (adjacentRight j))
    let e := ps (m (affineContractionWord C P j))
    let t := ps (m (aCrossing C j false))
    let ti := ps (m (aCrossing C j true))
    let v := multiplicativeResolvent a
    let w := multiplicativeResolvent b
    let g := pairResolvent (a*b)
    let qi := ps (algebraMap C (AW C P (i+1)) (↑P.Q⁻¹ : C))
    let q2 := ps (algebraMap C (AW C P (i+1)) ((P.Q : C)^2))
    let c := ps (algebraMap C (AW C P (i+1)) (2-(P.q : C)^2-(↑P.q⁻¹ : C)^2))
    (e*w-t*qi-g)*(e*v+ti*qi-g) = -(qi^2*(1+c*(g+g^2))) ∧
    (w+t*qi-e*g)-q2*(v+1)*(w+t*qi-e*g)*v =
      (t*v*ti+t*qi-e*g)-q2*w*(e*v*e+ps (algebraMap C (AW C P (i+1)) (P.z : C))*e*qi-e*g)*(w+1) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
