-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_abstract_product
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.abstract_product
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:06:34.479814+00:00
-- url     : https://prove2.me/theorems/30f63b7e-46c0-4e15-8c10-b0491868bba8
-- title:
--   Abstract regularised calculus product formula
-- statement:
--   Let $X$ be a complex Banach space, $F$ a commutative unital complex algebra, $E\subset F$ a possibly nonunital subalgebra, and $\Phi:E\to\mathcal L(X)$ a proper algebra representation. Extend $\Phi$ by injective regularisation; write $F_r$ for regularisable symbols and $F_b$ for those with bounded, everywhere-defined values. Suppose $f,g,f^{-1}\in F_r$, and there are $e_1,e_2,e_3\in F_b$ whose algebra inverses belong to $F_r$, with $e_1f,e_2g,e_3f^{-1}\in F_b$. For a complex polynomial $p$ with $p(0)\ne0$, assume $\operatorname{ran}\Phi(p(e_3))\subseteq\operatorname{ran}\Phi(e_1e_2)$. Then
--
--   $$\Phi(f)\Phi(g)=\Phi(fg).$$
--
--   This is equality of operator graphs, including the natural domains; composition applies the right factor first. It is the abstract product criterion used by the paper's concrete calculi.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 7, Theorem 2.5

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

/-- Theorem 2.5, PDF p.7. Every e_j has an algebra inverse in Fr;
the polynomial has nonzero constant term and ranges are actual ranges. -/
theorem abstract_product [CompleteSpace X] (C : ElementaryCalculus F X) (hC : IsProper C)
    (f g q e1 e2 e3 : F)
    (hf : Regularisable C f) (hg : Regularisable C g)
    (hq : RegularInverse C f q)
    (he1 : Regularisable C e1 ∧ e1 ∈ boundedElements (calculusValue C))
    (he2 : Regularisable C e2 ∧ e2 ∈ boundedElements (calculusValue C))
    (he3 : Regularisable C e3 ∧ e3 ∈ boundedElements (calculusValue C))
    (hi1 : ∃ r, RegularInverse C e1 r) (hi2 : ∃ r, RegularInverse C e2 r)
    (hi3 : ∃ r, RegularInverse C e3 r)
    (h1 : Regularisable C (e1 * f) ∧ (e1 * f) ∈ boundedElements (calculusValue C))
    (h2 : Regularisable C (e2 * g) ∧ (e2 * g) ∈ boundedElements (calculusValue C))
    (h3 : Regularisable C (e3 * q) ∧ (e3 * q) ∈ boundedElements (calculusValue C))
    (p : Polynomial ℂ) (hp : p.eval 0 ≠ 0)
    (hrange : graphRange (calculusValue C (Polynomial.aeval e3 p)) ⊆
      graphRange (calculusValue C (e1 * e2))) :
    graphMul (calculusValue C f) (calculusValue C g) = calculusValue C (f * g) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
