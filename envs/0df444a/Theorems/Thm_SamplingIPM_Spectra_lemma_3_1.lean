-- Prove2me | Theorems.Thm_SamplingIPM_Spectra_lemma_3_1
-- name    : SamplingIPM.Spectra.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:44.639738+00:00
-- url     : https://prove2.me/theorems/b3c02146-93ea-4c5e-9907-9c8b483ccc44
-- title:
--   Lemma 3.1, p. 11 — a convex body with identity uniform covariance lies in a ball of radius n + 1
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body and let $\Sigma(0)$ be the covariance matrix of the uniform distribution over $K$ (the Boltzmann distribution with parameter $0$). If
--   $$\Sigma(0)=I,$$
--   that is, $\langle h,\Sigma(0)k\rangle=\langle h,k\rangle$ for all $h,k\in\mathbb R^n$, then there is a point $c\in\mathbb R^n$ with
--   $$K\subseteq\{x\in\mathbb R^n:\ \|x-c\|\le n+1\}.$$
--
--   This is Theorem 4.1 of Kannan, Lovász and Simonovits, cited by the paper. It converts an assumption on the second moments of the uniform distribution into a bound on the size of $K$, and it is the input to Lemma 3.2.
--
--   **Formalization Note** The centre of the ball is existential, as in the paper's statement; the ball is closed.
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, p. 11, Lemma 3.1 (Theorem 4.1 in Kannan–Lovász–Simonovits 1995)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open EntropicBarrier.Universal

namespace SamplingIPM.Spectra

theorem lemma_3_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (hiso : ∀ h k : EuclideanSpace ℝ (Fin n), covForm K 0 h k = ⟪h, k⟫) :
    ∃ c : EuclideanSpace ℝ (Fin n), K ⊆ Metric.closedBall c ((n : ℝ) + 1) := by sorry

end SamplingIPM.Spectra
