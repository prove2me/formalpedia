-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_regularizer_product
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.regularizer_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:09:03.90792+00:00
-- url     : https://prove2.me/theorems/17953464-b495-4645-8347-7aae6164eed9
-- title:
--   Product formula with injective elementary regularisers
-- statement:
--   Let $(E,F,\Phi)$ be a proper abstract functional calculus on a complex Banach space, extended by injective regularisation. Let $f,g,f^{-1}\in F_r$, with $e_1\in\operatorname{Reg}(f)$, $e_2\in\operatorname{Reg}(g)$ and $e_3\in\operatorname{Reg}(f^{-1})$. Thus each $e_j$ and its stated regularised product belong to $E$, and each $\Phi(e_j)$ is injective. If a complex polynomial $p$ has $p(0)\ne0$ and $\operatorname{ran}\Phi(p(e_3))\subseteq\operatorname{ran}\Phi(e_1e_2)$, then
--
--   $$\Phi(f)\Phi(g)=\Phi(fg).$$
--
--   This is equality on the natural domains. Algebra inverses of the regularisers are unnecessary in this variant.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 8, Corollary 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ContDiff NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P11

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore restrictGraph)

universe u v w

variable {F : Type u} [CommRing F] [Algebra ℂ F]

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Corollary 2.6, PDF p.8. The e_j are injective regularisers;
no algebra inverses for them are required. -/
theorem regularizer_product [CompleteSpace X] (C : ElementaryCalculus F X) (hC : IsProper C)
    (f g q e1 e2 e3 : F)
    (hf : Regularisable C f) (hg : Regularisable C g)
    (hq : RegularInverse C f q)
    (h1 : IsRegularizer C f e1) (h2 : IsRegularizer C g e2)
    (h3 : IsRegularizer C q e3)
    (p : Polynomial ℂ) (hp : p.eval 0 ≠ 0)
    (hrange : graphRange (calculusValue C (Polynomial.aeval e3 p)) ⊆
      graphRange (calculusValue C (e1 * e2))) :
    graphMul (calculusValue C f) (calculusValue C g) = calculusValue C (f * g) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
