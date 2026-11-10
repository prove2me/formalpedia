-- Prove2me | Theorems.Thm_TightReleaseSchedules_Stationary_anchored_cross_moments
-- name    : TightReleaseSchedules.Stationary.anchored_cross_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:43:55.149256+00:00
-- url     : https://prove2.me/theorems/9b9fd965-a9a8-4195-a9ea-19603eb45490
-- title:
--   Lemma 3.3 — Anchored cross-moments
-- statement:
--   Let $T,d\ge1$, fix $\theta_0\in\mathbb R^d$, and let $\theta_1,\ldots,\theta_T$ be a deterministic path with $\beta_i=\theta_i-\theta_0$ satisfying $\|\beta_i\|_2\le1$. In the independent Gaussian regression experiment, set $Z_i=X_i(Y_i-X_i^\top\theta_0)$. These vectors have finite first and second moments and satisfy
--
--   $$
--   \mathbb EZ_i=\beta_i,\qquad
--   \operatorname{Cov}(Z_i)=(1+\|\beta_i\|_2^2)I_d+\beta_i\beta_i^\top,\qquad
--   \operatorname{tr}\operatorname{Cov}(Z_i)\le2d+1.
--   $$
--   For every deterministic nonempty set $I$ of $w=|I|$ rounds, write $\bar\beta_I=w^{-1}\sum_{i\in I}\beta_i$. For every closed convex set $K\subseteq\mathbb R^d$ containing $\bar\beta_I$,
--
--   $$
--   \mathbb E\left\|\Pi_K\!\left(\frac1w\sum_{i\in I}Z_i\right)-\bar\beta_I\right\|_2^2
--   \le\min\left\{\frac{2d+1}{w},\operatorname{diam}(K)^2\right\}.
--   $$
--   This is the deterministic-window estimation result used by Algorithm 1. It applies to general target paths and to unbounded closed convex sets, whose extended diameter is infinite.
--
--   Differences from the source:
--   - encoding: positive integer rounds and dimensions, and a defined nonempty window average → Fin T and Fin d with T,d positive, I.Nonempty and w=I.card; reason: index zero denotes source round one and all defined source windows occur
--   - encoding: a mean and a covariance matrix with finite Gaussian moments → explicit first- and second-moment integrability conclusions and coordinatewise covariance and trace formulas; reason: these express the existence and entries of exactly the stated Gaussian moments
--   - encoding: an expectation and the diameter of an arbitrary closed convex set → nonnegative extended expectation and Metric.ediam, including infinite diameter; reason: unbounded K is retained and nonintegrable loss cannot default to zero
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Lemma 3.3, printed p.7, PDF p.8

import Definitions.Def_TightReleaseSchedules_Stationary_gaussian_experiment

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TightReleaseSchedules.Stationary

/-- Lemma 3.3, all moment and general closed-convex projection clauses. -/
theorem anchored_cross_moments (T d : ℕ) (hT : 0 < T) (hd : 0 < d)
    (θ₀ : Vector d) (θ : Fin T → Vector d) (hβ : ∀ i, ‖θ i - θ₀‖ ≤ 1) :
    (∀ i,
      Integrable (fun z => crossMoment θ₀ (observations θ z i)) (gaussianRows T d) ∧
      Integrable (fun z => ‖crossMoment θ₀ (observations θ z i)‖ ^ 2) (gaussianRows T d) ∧
      (∫ z, crossMoment θ₀ (observations θ z i) ∂(gaussianRows T d)) = θ i - θ₀ ∧
      (∀ k l, crossCovariance θ₀ θ i k l =
        (1 + ‖θ i - θ₀‖ ^ 2) * (if k = l then 1 else 0) +
          (θ i - θ₀) k * (θ i - θ₀) l) ∧
      (∑ k : Fin d, crossCovariance θ₀ θ i k k) ≤ 2 * (d : ℝ) + 1) ∧
    (∀ (I : Finset (Fin T)), I.Nonempty → ∀ K : Set (Vector d),
      IsClosed K → Convex ℝ K → pathAverage (fun i => θ i - θ₀) I ∈ K →
      (∫⁻ z, ENNReal.ofReal
        (‖convexProjection K (anchoredAverage θ₀ I (observations θ z)) -
          pathAverage (fun i => θ i - θ₀) I‖ ^ 2) ∂(gaussianRows T d)) ≤
        min (ENNReal.ofReal ((2 * (d : ℝ) + 1) / I.card)) (Metric.ediam K ^ 2)) := by sorry

end TightReleaseSchedules.Stationary
