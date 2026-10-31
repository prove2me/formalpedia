-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_process_cameronMartin
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.process_cameronMartin
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:39:28.550354+00:00
-- url     : https://prove2.me/theorems/b6bcd7dd-a2dc-41a5-aca9-e1ce9f0981f1
-- title:
--   Lemma 3.1
-- statement:
--   For a centered Gaussian process $W$ on an arbitrary index set $T$, let $P^W$ and $P^{W+f}$ denote its laws on the product sigma algebra of $\mathbb R^T$. For every $f$ in its covariance RKHS, the two laws are mutually absolutely continuous and
--   $$\frac{dP^{W+f}}{dP^W}(W)=\exp\{Uf-\tfrac12\|f\|_H^2\}\quad P\text{-a.s.}$$
--   Here $Uf$ is the canonical first-chaos $L^2(P)$ class. This gives the process form of the Cameron–Martin density.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 8, Lemma 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section ProcessResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- Lemma 3.1, arXiv:0805.3252v1, PDF p.8.
Product measurable space, not the Borel sigma algebra of an uncountable product. The identity uses an a.e. representative of U f. -/
theorem process_cameronMartin
{T : Type v} (W : T → Omega → ℝ) (hW : CenteredProcess P W)
    (f : T → ℝ) (hf : f ∈ processRKHS P W) :
    (P.map (fun o t => W t o + f t)) ≪ (P.map (fun o t => W t o)) ∧
    (P.map (fun o t => W t o)) ≪ (P.map (fun o t => W t o + f t)) ∧
    ∀ᵐ o ∂P,
      (((P.map (fun o t => W t o + f t)).rnDeriv
        (P.map (fun o t => W t o))) (fun t => W t o)).toReal =
      Real.exp ((processLift P W f) o - (processNorm P W f) ^ 2 / 2) := by sorry

end ProcessResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
