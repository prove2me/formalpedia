-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_gamma_product_integral
-- name    : QAlgorithms.Papers.Independent.Support21.P08.gamma_product_integral
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:27:10.64929+00:00
-- url     : https://prove2.me/theorems/ce16e7b7-fe87-4ac3-8a2d-a18ebc424642
-- title:
--   The product of seminormal coefficients is integral
-- statement:
--   Let $R$ be a commutative integral domain, $K=\operatorname{Frac}(R)$, and let a finite cellular $R$-algebra and its scalar extension carry the same JM family and contents under their basis-compatible inclusion. Assume complete generic content-sequence separation. Let $\gamma_t\in K$ be the computed seminormal structure coefficients. For each shape $\lambda$,
--
--   $$\prod_{t\in T(\lambda)}\gamma_t\in R\subseteq K.$$
--
--   Only the product is asserted integral; individual coefficients need not belong to $R$.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 13, 3.14

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section IntegralForm

variable {R K AR AK Shape : Type*} [CommRing R] [integralDomain : IsDomain R] [Field K]

variable [Algebra R K] [integralFraction : IsFractionRing R K]

variable [Ring AR] [Algebra R AR] [Ring AK] [Algebra K AK] [Algebra R AK]

variable [integralTower : IsScalarTower R K AK] [Fintype Shape] [PartialOrder Shape]

variable {T : Shape → Type*} [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable (DR : CellDatum (R := R) (A := AR) (T := T))

variable (DK : CellDatum (R := K) (A := AK) (T := T))

include integralDomain integralFraction integralTower in
/-- Corollary 3.14, PDF p.13. The basis-compatible algebra map explicitly
identifies the R-form and its scalar extension. Only the PRODUCT is integral.
Uses complete content-sequence separation, correcting Definition 2.8. -/
theorem gamma_product_integral {M : ℕ} (JR : JMFamily DR M) (JK : JMFamily DK M)
    (inc : AR →ₐ[R] AK)
    (hbasis : ∀ z, inc (DR.basis z) = DK.basis z)
    (hL : ∀ i, inc (JR.L i) = JK.L i)
    (hc : ∀ t i, algebraMap R K (JR.content t i) = JK.content t i)
    (hsep : separatesAll JR) (l : Shape) :
    ∃ r : R, algebraMap R K r = ∏ t : T l, seminormalGamma JK ⟨l, t⟩ := by sorry

end IntegralForm

end QAlgorithms.Papers.Independent.Support21.P08

end
