-- Prove2me | Theorems.Thm_StochSeedEval_Hajek_joint_clt
-- name    : StochSeedEval.Hajek.joint_clt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:11.91805+00:00
-- url     : https://prove2.me/theorems/2b53c911-342c-44e2-985b-0c2e7cd45c6f
-- title:
--   Proof of Proposition 2, p. 40 — joint central limit theorem in Cramér–Wold form
-- statement:
--   Let $\widehat\beta_N=(\bar w_{A,N},\bar w_{B,N},\overline{w_Ay}_N,\overline{w_By}_N)$ and $\beta=(1,1,\mu_A,\mu_B)$. Suppose the design covers both strategies' supports, each coordinate has a finite second moment, and the observed seed sets are independent with common design law. For every vector $c\in\mathbb R^4$,
--
--   $$\sqrt N\,c^\top(\widehat\beta_N-\beta)\Rightarrow\mathcal N\!\left(0,\operatorname{Var}_\Delta(c_1w_A+c_2w_B+c_3w_Ay+c_4w_By)\right).$$
--
--   This is the scalar projection form of the joint Gaussian limit stated in Appendix A.2; all choices of $c$ are included.
--
--   **Formalization Note.** The source's covariance display labels entries with $\sqrt N\operatorname{Var}$, whereas the fixed covariance of the Gaussian limit is the single-observation covariance, equivalently the limit of $N$ times each sample-average covariance. The statement uses that covariance.
-- source:
--   Chin, Eckles & Ugander, Evaluating Stochastic Seeding Strategies in Networks, arXiv:1809.09561v3, p. 40, proof of Proposition 2, √N(β̂−β) ⇒ N(0,Σ) (Cramér–Wold form)

import Mathlib
import Definitions.Def_StochSeedEval_Hajek_Estimators

open MeasureTheory ProbabilityTheory Filter Topology

namespace StochSeedEval.Hajek

/-- Every scalar projection of the four-dimensional CLT, proof of Proposition 2, p. 40. -/
theorem joint_clt
    {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hA2 : MemLp (weightA pA pD) 2 pD.toMeasure)
    (hB2 : MemLp (weightB pB pD) 2 pD.toMeasure)
    (hAy2 : MemLp (fun s => weightA pA pD s * y s) 2 pD.toMeasure)
    (hBy2 : MemLp (fun s => weightB pB pD s * y s) 2 pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) :
    ∀ (c : Fin 4 → ℝ) {Ω'' : Type*} [MeasurableSpace Ω'']
      (Q : Measure Ω'') [IsProbabilityMeasure Q] (Z : Ω'' → ℝ),
      HasLaw Z (gaussianReal 0 (variance (linearStatistic pA pB pD y c) pD.toMeasure).toNNReal) Q →
      TendstoInDistribution
        (fun (N : ℕ) ω => Real.sqrt (N : ℝ) *
          (c 0 * (sampleAverage S (weightA pA pD) N ω - 1) +
           c 1 * (sampleAverage S (weightB pB pD) N ω - 1) +
           c 2 * (sampleAverage S (fun s => weightA pA pD s * y s) N ω - meanA pA y) +
           c 3 * (sampleAverage S (fun s => weightB pB pD s * y s) N ω - meanB pB y)))
        atTop Z (fun _ => P) Q := by sorry

end StochSeedEval.Hajek
