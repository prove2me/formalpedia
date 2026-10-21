-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_quotient_calculus
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.quotient_calculus
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:08:29.525798+00:00
-- url     : https://prove2.me/theorems/38bfa0ab-95e1-46d3-b197-c01cd37d2063
-- title:
--   Regularised calculus passes through bounded quotients
-- statement:
--   Let $(E,F,\Phi)$ and $(E,F,\Phi_0)$ be proper abstract functional calculi on complex Banach spaces $X$ and $Y$. Let $u:X\to Y$ be a bounded complex-linear surjection satisfying $\Phi_0(a)u=u\Phi(a)$ for all $a\in E$. Suppose $e\in\operatorname{Reg}_{\Phi}(f)$ and $\Phi(e)(\ker u)=\ker u$. Then $e\in\operatorname{Reg}_{\Phi_0}(f)$ and
--
--   $$\Phi_0(f)u=u\Phi(f),\qquad \operatorname{dom}\Phi_0(f)=u(\operatorname{dom}\Phi(f)).$$
--
--   The intertwining identity is an equality of graphs from $X$ to $Y$, and the kernel hypothesis is surjectivity onto the kernel. The result transfers the extended calculus through a quotient.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 6, Proposition 2.4

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

/-- Proposition 2.4, PDF pp.6–7. Onto the kernel means set equality;
the conclusion contains both graph intertwining and the full domain image. -/
theorem quotient_calculus [CompleteSpace X] [CompleteSpace Y] (C : ElementaryCalculus F X) (D : ElementaryCalculus F Y)
    (hC : IsProper C) (hD : IsProper D) (hE : D.elementary = C.elementary)
    (u : X →L[ℂ] Y) (hu : Function.Surjective u)
    (hint : ∀ g ∈ C.elementary, (D.rho g).comp u = u.comp (C.rho g))
    (f e : F) (he : IsRegularizer C f e)
    (hker : (C.rho e) '' (u.ker : Set X) = (u.ker : Set X)) :
    IsRegularizer D f e ∧
    graphPrecompose (calculusValue D f) u = graphPostcompose u (calculusValue C f) ∧
    graphDomain (calculusValue D f) = u '' graphDomain (calculusValue C f) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
