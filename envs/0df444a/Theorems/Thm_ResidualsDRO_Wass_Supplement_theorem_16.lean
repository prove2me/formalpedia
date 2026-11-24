-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_theorem_16
-- name    : ResidualsDRO.Wass.Supplement.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:43:36.787175+00:00
-- url     : https://prove2.me/theorems/3867e043-63b7-44e4-99c6-73170a33a1e1
-- title:
--   Theorem 16 (corrected: source/boundary conventions) — optimizer-set consistency
-- statement:
--   Under the hypotheses of Proposition 15, let vhat_n(x) and Shat_n(x) be the optimal value and entire optimal solution set of the unified ER-DRO problem. Then
--
--   $$\widehat v_n(x)\xrightarrow{p}v^*(x),\qquad D(\widehat S_n(x),S^*(x))\xrightarrow{p}0,\qquad\sup_{z\in\widehat S_n(x)}g(z;x)\xrightarrow{p}v^*(x).$$
--
--   The deviation is one-sided: D(A,B)=sup_{z∈A} inf_{u∈B}‖z−u‖. The last assertion concerns all optimal solutions. Lean states it as the extended supremum of the nonnegative gaps g(z;x)−v*(x). Since all feasible true costs are at least v* and Shat_n is nonempty, this is exactly the third displayed convergence, including the possibility of an infinite supremum before convergence. It is not replaced by a claim about one selection.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: measurable regression estimates and optimal selections → outer probabilities permit arbitrary selections satisfying the same optimality equalities; reason: all probability bounds follow from pathwise containment in the displayed measurable bounding events; measurable source selections are included
--   - correction: Assumption 12 or 16 has positive squared-simplex equality for every n → the literal equality is required for all sufficiently large n; reason: at n=1 the simplex is {(1)} and its squared deviation is zero; the source convergence arguments are asymptotic, pp. 21, 23, 25
--   - generalization: a family of probability sets parameterized by radius with limit (9) → nonempty simplex-valued sets along the sequence, with the required Assumption 12/16 equality, without prescribing unused off-sequence sets; reason: the proof and conclusions only use these sets along the sequence; every source family gives such a sequence
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 23, Theorem 16

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Full source conclusion, at a fixed covariate satisfying the almost-everywhere hypotheses; sample sizes start at one. -/
theorem theorem_16
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (ps : E dx → (n : ℕ) → Set (Fin n → ℝ)) (μ : E dx → ℕ → ℝ)
    (L : E dz → ℝ) (Cζ ρ : ℝ) (h : UAssumptions M P x ps μ L Cζ ρ)
    : Vanishes P (fun n ω => error (uvalue M ps μ x n ω) (vstar M x)) ∧
    Vanishes P (fun n ω => deviation (usolutions M ps μ x n ω) (solutions M x)) ∧
    Vanishes P (fun n ω => ⨆ z ∈ usolutions M ps μ x n ω,
      error (g M x z) (vstar M x)) := by sorry

end ResidualsDRO.Wass.Supplement
