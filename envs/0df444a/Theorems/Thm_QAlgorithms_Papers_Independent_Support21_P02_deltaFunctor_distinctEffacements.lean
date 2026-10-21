-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P02_deltaFunctor_distinctEffacements
-- name    : QAlgorithms.Papers.Independent.Support21.P02.deltaFunctor_distinctEffacements
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:27:57.858344+00:00
-- url     : https://prove2.me/theorems/42da7eea-9a0f-40da-aff0-a49d516990c8
-- title:
--   Remark VI.3: distinct effacements suffice
-- statement:
--   Let $\mathcal C$ be a category with distinguished short exact sequences, and let $H,K$ be cohomological $\delta$-functors from $\mathcal C$ to abelian groups, without assuming that the degree-zero functors are left exact. Suppose there are two functorial distinguished sequences
--   $$
--   A\longrightarrow I(A)\longrightarrow U(A),\qquad
--   A\longrightarrow I'(A)\longrightarrow U'(A)
--   $$
--   such that $H^j(I(A))=0$ and $K^j(I'(A))=0$ for all objects $A$ and all $j\ge1$. Assume that at least one of these pairs has the compatible quotients specified in Theorem VI.2(2): for each $A\xrightarrow f B\xrightarrow g C$, there are a distinguished $A\to I(B)\xrightarrow q Q$ and maps $\beta:U(A)\to Q$, $\gamma:C\to Q$ with $\beta\zeta_A=qI(f)$ and $\gamma g=q\iota_B$, or the corresponding primed data.
--
--   Every natural isomorphism $\alpha:H^0\cong K^0$ extends to mutually inverse morphisms of $\delta$-functors $\varphi:H\to K$ and $\psi:K\to H$. In every degree, including zero,
--   $$
--   \psi^j\varphi^j=\mathrm{id}_{H^j},\qquad
--   \varphi^j\psi^j=\mathrm{id}_{K^j}.
--   $$
--   Their degree-zero components are $\alpha$ and $\alpha^{-1}$. Moreover, any degreewise natural family extending $\alpha$ and commuting with the connecting maps of the unprimed resolution equals $\varphi$; the corresponding assertion for $\alpha^{-1}$ and the primed resolution gives $\psi$.
--
--   Thus two different effacement constructions suffice to identify the entire cohomology theories, including their connecting homomorphisms.
-- source:
--   A Cocycle Model for Topological and Lie Group Cohomology, arXiv:1110.3304v3, PDF p. 26, Remark VI.3: distinct effacements suffice

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P02

universe u v w

namespace QAlgorithms.Papers.Independent.Support21.P02

open CategoryTheory

/-- Remark VI.3, PDF pp. 26--27: distinct positive-degree effacements
suffice. Quotient compatibility is required for at least one of them.
The resulting transformations extend alpha and its inverse, are inverse
in every degree including zero, and commute with arbitrary connecting
maps. The final clauses identify them with every family obtained by the
resolution-square construction, without assuming that family is already
a morphism of delta-functors. -/
theorem deltaFunctor_distinctEffacements
    {C : Type u} [Category.{v} C] (S : SequenceClass C)
    (R Rprime : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S)
    (hH : ∀ (A : C) (n : ℕ), 1 ≤ n →
      Limits.IsZero ((H.degree n).obj (R.I.obj A)))
    (hK : ∀ (A : C) (n : ℕ), 1 ≤ n →
      Limits.IsZero ((K.degree n).obj (Rprime.I.obj A)))
    (hquot : CompatibleQuotients R ∨ CompatibleQuotients Rprime)
    (alpha : H.degree 0 ≅ K.degree 0) :
    ∃ e : DeltaEquivalence H K,
      e.forward.component 0 = alpha.hom ∧
      e.backward.component 0 = alpha.inv ∧
      (∀ phi : DegreeFamily H K,
        ResolutionExtension R alpha.hom phi → phi = e.forward.toDegreeFamily) ∧
      (∀ psi : DegreeFamily K H,
        ResolutionExtension Rprime alpha.inv psi → psi = e.backward.toDegreeFamily) := by sorry

end QAlgorithms.Papers.Independent.Support21.P02
