-- Prove2me | Theorems.Thm_PrescAnalytics_KNN_theorem_5_knn_asymptotically_optimal
-- name    : PrescAnalytics.KNN.theorem_5_knn_asymptotically_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:42:00.701289+00:00
-- url     : https://prove2.me/theorems/1bf0a819-a3fb-433a-a84a-f51a5d3a60f4
-- title:
--   Theorem 5 (kNN) — the k-nearest-neighbour predictive prescription is asymptotically optimal and consistent
-- statement:
--   Let $(x^1,y^1),(x^2,y^2),\dots$ be independent and identically distributed with law $\mu$ of $(X,Y)$ on $\mathbb R^{d_x}\times\mathbb R^{d_y}$, with $X\in\mathcal X$ and $Y\in\mathcal Y$ almost surely. Let $c:\mathbb R^{d_z}\times\mathbb R^{d_y}\to\mathbb R$ be a cost and $\mathcal Z\subseteq\mathbb R^{d_z}$ a feasible set satisfying Assumptions 3 (existence), 4 (continuity) and 5 (regularity, in either of its two cases). Let $w_{N,i}(x)$ be the kNN weights (12) with
--   $$k=\min\big\{\lceil CN^\delta\rceil,\ N-1\big\},\qquad C>0,\ 0<\delta<1,$$
--   and let $\hat z_N(x)\in\arg\min_{z\in\mathcal Z}\sum_{i=1}^N w_{N,i}(x)\,c(z;y^i)$ as in (3). Then $\hat z_N(x)$ is asymptotically optimal and consistent: with probability 1, for $\mu_X$-almost every $x$,
--   $$\lim_{N\to\infty}\mathbb E\big[c(\hat z_N(x);Y)\mid X=x\big]=v^*(x)\qquad\text{and}\qquad \lim_{N\to\infty}\ \inf_{z\in\mathcal Z^*(x)}\|\hat z_N(x)-z\|=0 .$$
--
--   This is the paper's central asymptotic guarantee for its local predictive prescriptions: using only data and a nearest-neighbour reweighting, the decision's true conditional cost approaches the full-information optimum $v^*(x)$ of problem (2), and the decision itself approaches the set of full-information optimizers. It covers unbounded feasible sets such as the newsvendor's $\mathcal Z=[0,\infty)$ through case 2 of Assumption 5.
--
--   **Formalization Note** The conclusion is Definition 1 for the set-valued rule $N,\omega,x\mapsto\arg\min_{z\in\mathcal Z}\widehat C_N(z\mid x)$: almost surely, for $\mu_X$-a.e. $x$, $\mathcal Z^*(x)$ and this argmin are nonempty for all large $N$ and **every** sequence $z_N$ that lies in this argmin for all large $N$ satisfies $C(z_N\mid x)\to C(z^\star\mid x)$ for every $z^\star\in\mathcal Z^*(x)$ and $\operatorname{dist}(z_N,\mathcal Z^*(x))\to0$. Quantifying over every selection, inside the almost-sure quantifiers, is the paper's "$\hat z_N(x)$ as in (3)" (an arbitrary element of the argmin) and avoids measurable-selection questions; "for all large $N$" allows the argmin to be empty for small $N$ in case 2; eventual nonemptiness keeps the set-valued statement from being vacuous. $E[c(\hat z_N(x);Y)\mid X=x]$ is $C(\hat z_N(x)\mid x)$: the decision is frozen and the true conditional cost is taken, against the version `μ.condKernel x`. The paper's "for every $x\in\mathcal X$" in Assumption 5 refers to this version. The data are a measurable, mutually independent (`iIndepFun`) sequence, each term with law $\mu$; samples are indexed from $0$. The tie rule is lower-index-first. All other conventions are those of the definition file.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 19, Theorem 5 (restated with iid sampling as Theorem 15, p. 43; proof p. 47)

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace PrescAnalytics.KNN

/-- **Theorem 5 (kNN)** = Theorem 15 (iid case), arXiv:1402.5481v4, pp. 19, 43. Under Assumptions
3, 4 and 5 and iid data `(x^i, y^i) ~ μ`, the predictive prescription (3) with the kNN weights (12),
`k = min {⌈C N^δ⌉, N - 1}`, `C > 0`, `0 < δ < 1`, is asymptotically optimal and consistent
(Definition 1), for every selection from its argmin. -/
theorem theorem_5_knn_asymptotically_optimal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))
    (hS_meas : ∀ i, Measurable (S i)) (hS_indep : iIndepFun S P)
    (hS_law : ∀ i, P.map (S i) = μ)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (Xs : Set (EuclideanSpace ℝ (Fin dx))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (hXs : ∀ᵐ p ∂μ, p.1 ∈ Xs) (hYs : ∀ᵐ p ∂μ, p.2 ∈ Ys)
    (h3 : Assumption3 μ c Z) (h4 : Assumption4 c Z Ys) (h5 : Assumption5 μ c Z Xs Ys)
    (C δ : ℝ) (hC : 0 < C) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    IsAsymptoticallyOptimal P μ c Z (knnArgmin C δ c Z S) ∧
      IsConsistent P μ c Z (knnArgmin C δ c Z S) := by sorry

end PrescAnalytics.KNN
