-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_arbitrary_baire_product
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_arbitrary_baire_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:17:24.395574+00:00
-- url     : https://prove2.me/theorems/c11a7a21-2db7-42c5-86e1-e59acef3499f
-- title:
--   Remark 6.8, unnumbered theorem: arbitrary Baire products
-- statement:
--   Let $(X_i)_{i\in I}$ be any family of compact Hausdorff spaces and let $\Phi_i$ be Baire calculi on them acting on one Hilbert space $H$. Suppose $\Phi_i(f)$ and $\Phi_j(g)$ commute for every pair $i,j$ and every bounded Baire $f,g$. Then there is a unique Baire calculus $P$ on $\prod_iX_i$ such that
--
--   $$P\!\left(\prod_{i\in F} f_i\circ\pi_i\right)=\prod_{i\in F}\Phi_i(f_i)$$
--
--   for every finite support $F\subseteq I$ and bounded Baire symbols $f_i$ equal to one outside $F$. Here $\pi_i$ is coordinate projection. Products on the right may be taken in any listing of the distinct indices, since all factors commute. The finite tensor is a Baire measurable symbol. Empty products are the constant one and the operator identity.
--
--   This is the precise arbitrary Baire product theorem; it does not assert the unspecified Borel analogue.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 29, Remark 6.8, unnumbered theorem: arbitrary Baire products

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Remark 6.8, PDF pp.29–30: arbitrary compact Hausdorff Baire products.
The finite tensor is constructed in the conclusion. The empty list gives 1 and I.
Source correction (independently audited in moderation round 1).
Printed: The arbitrary-product theorem quantifies lambda,nu while the displayed commutation equation uses lambda,mu.
Changed: Quantify both indices occurring in the equation consistently, as all pairs i,j.
Why: The commutation assertion must bind both factor indices. This is only an index-name repair; compact Hausdorff bases, Baire sigma algebras, arbitrary index family and finite support are unchanged.
-/
theorem calculus_arbitrary_baire_product {I : Type u} {Z : I → Type v}
    [∀ i, TopologicalSpace (Z i)] [∀ i, CompactSpace (Z i)] [∀ i, T2Space (Z i)]
    (hH : CompleteSpace H)
    (F : ∀ i, @Symbol (Z i) k (baire k (Z i)) _ → Relation H)
    (hF : ∀ i, letI : MeasurableSpace (Z i) := baire k (Z i); Calculus (F i))
    (hcomm : letI : ∀ i, MeasurableSpace (Z i) := fun i => baire k (Z i)
      ∀ i j, ∀ f : @Symbol (Z i) k (baire k (Z i)) _,
      ∀ g : @Symbol (Z j) k (baire k (Z j)) _, BoundedSymbol f → BoundedSymbol g →
        mul (F i f) (F j g) = mul (F j g) (F i f)) :
    letI : MeasurableSpace (∀ i, Z i) := baire k (∀ i, Z i)
    letI : ∀ i, MeasurableSpace (Z i) := fun i => baire k (Z i)
    ∃! P : Symbol (∀ i, Z i) k → Relation H,
      Calculus P ∧
      ∀ (L : List I), L.Nodup → ∀ f : ∀ i, @Symbol (Z i) k (baire k (Z i)) _,
        (∀ i, BoundedSymbol (f i)) → (∀ i, i ∉ L → f i = constant 1) →
        ∃ s : @Symbol (∀ i, Z i) k (baire k (∀ i, Z i)) _,
          s.val = (fun x => (L.map fun i => (f i).val (x i)).prod) ∧
          P s = productGraphs (L.map fun i => F i (f i)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
