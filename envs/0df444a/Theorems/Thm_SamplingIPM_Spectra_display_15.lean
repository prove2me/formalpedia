-- Prove2me | Theorems.Thm_SamplingIPM_Spectra_display_15
-- name    : SamplingIPM.Spectra.display_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:48.056875+00:00
-- url     : https://prove2.me/theorems/f953b72f-67f3-4691-b58d-545ba8765929
-- title:
--   Display (15), p. 12 — halving the local norm along θ_k: ‖v‖_θ ≥ 2^{−m} ‖v‖_{θ_m}
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body, let $f^*$ be its entropic barrier (the Fenchel conjugate of the log partition function), and let $\vartheta>0$ be a complexity parameter for $f^*$, in the sense that $Df^*(x)[h]\le\sqrt{\vartheta\,D^2f^*(x)[h,h]}$ for all $x\in\operatorname{int}K$ and $h\in\mathbb R^n$. For $\theta\in\mathbb R^n$ set $\theta_k=(1-\frac1{2\sqrt\vartheta+1})^k\theta$. Then for every $\theta$ and every $k\ge1$,
--   $$\|\theta_{k-1}-\theta_k\|_{\theta_k}\le\frac12,$$
--   and for every $m\ge0$ and every $v\in\mathbb R^n$,
--   $$\|v\|_\theta=\|v\|_{\theta_0}\ \ge\ 2^{-m}\,\|v\|_{\theta_m}.$$
--
--   This is the halving chain in the proof of Theorem 3.1: it moves a lower bound on the local norm from the small parameter $\theta_m$ back to $\theta$, at the price of a factor $2^{-m}$.
--
--   **Formalization Note** The complexity parameter enters through the published predicate `SatisfiesNuBound K (entropicBarrier K) ϑ`, equivalent to Definition 2.2's $\vartheta\ge\sup_x\|g^*_x(x)\|^{*2}_x$. The hypothesis $\vartheta>0$ is added: the paper's middle equality divides by $2\sqrt\vartheta$. The case hypothesis $\|\theta\|>1/(4R)$ of the paper is not used by (15) and is dropped; the claim is stated for every $\theta$. The first claim is indexed by $k+1$ for $k\ge0$.
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, p. 12, proof of Theorem 3.1, display (15)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_SamplingIPM_Spectra_Model

open scoped RealInnerProductSpace
open EntropicBarrier.Universal

namespace SamplingIPM.Spectra

theorem display_15 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : SatisfiesNuBound K (entropicBarrier K) ϑ) :
    (∀ (θ : EuclideanSpace ℝ (Fin n)) (k : ℕ),
      localNorm K (thetaSeq ϑ θ (k + 1)) (thetaSeq ϑ θ k - thetaSeq ϑ θ (k + 1)) ≤ 1 / 2) ∧
    (∀ (θ : EuclideanSpace ℝ (Fin n)) (m : ℕ) (v : EuclideanSpace ℝ (Fin n)),
      (2 : ℝ) ^ (-(m : ℤ)) * localNorm K (thetaSeq ϑ θ m) v ≤ localNorm K θ v) := by sorry

end SamplingIPM.Spectra
