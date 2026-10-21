-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_stieltjes_product
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.stieltjes_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:09:43.920585+00:00
-- url     : https://prove2.me/theorems/43337b68-3989-484a-8f3e-12ad5a97e432
-- title:
--   Positive Stieltjes orders add under multiplication
-- statement:
--   For $\alpha>0$, let $S_\alpha$ be the class of functions on $(0,\infty)$ represented by $f(z)=a+\int_{[0,\infty)}(z+t)^{-\alpha}\,\mu(dt)$, where $a\ge0$, $\mu$ is a positive Radon measure, and $\int(1+t)^{-\alpha}\,\mu(dt)<\infty$. If $\alpha,\beta>0$, $f\in S_\alpha$ and $g\in S_\beta$, then
--
--   $$fg\in S_{\alpha+\beta}.$$
--
--   The class includes constants and atoms at zero. The result supplies the scalar multiplication rule underlying the extended Stieltjes algebra.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 12, Lemma 4.1

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

/-- Lemma 4.1, PDF p.12: full positive Stieltjes classes multiply,
including the constant terms and zero atoms omitted by the cited special case. -/
theorem stieltjes_product (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta)
    (f g : PositiveReal → ℝ) (hf : f ∈ StieltjesClass alpha)
    (hg : g ∈ StieltjesClass beta) :
    (fun z => f z * g z) ∈ StieltjesClass (alpha + beta) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
