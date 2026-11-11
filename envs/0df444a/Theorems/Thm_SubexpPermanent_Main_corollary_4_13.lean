-- Prove2me | Theorems.Thm_SubexpPermanent_Main_corollary_4_13
-- name    : SubexpPermanent.Main.corollary_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:26.837757+00:00
-- url     : https://prove2.me/theorems/cf44fc6a-1de8-413f-9fa1-f62d429d7932
-- title:
--   Corollary 4.13 — projected steps along approximate directions: $f(\bar x)-f(z)\le\|x_0-z\|_2^2/(2\alpha T)+\alpha G^2/2+r$
-- statement:
--   Let $K\subseteq\mathbb R^m$ be nonempty, compact and convex, and $f:\mathbb R^m\to\mathbb R$ convex. Fix $z\in K$, an integer $T\ge1$, a step size $\alpha>0$, and $G,r\ge0$. Suppose $x_0,\dots,x_T\in K$ and $h_0,\dots,h_{T-1}\in\mathbb R^m$ satisfy, for every $0\le t<T$,
--   $$\|h_t\|_2\le G,\qquad f(z)\ge f(x_t)+\langle h_t,z-x_t\rangle-r,\qquad x_{t+1}=\Pi_K(x_t-\alpha h_t).$$
--   Then the average $\bar x=T^{-1}\sum_{t=0}^{T-1}x_t$ satisfies
--   $$f(\bar x)-f(z)\le\frac{\|x_0-z\|_2^2}{2\alpha T}+\frac{\alpha G^2}{2}+r .$$
--   It allows an additive error $r$ in each subgradient inequality, which is how §8 accounts for rational approximations of the edge probabilities.
--
--   Differences from the source:
--
--   - encoding: ℝ^m with the Euclidean norm and inner product → EuclideanSpace ℝ (Fin m); reason: the same space
--   - encoding: x_{t+1} = Π_K(x_t − α h_t) → IsEuclidProj K (x_t − α h_t) x_{t+1}: x_{t+1} is a point of K nearest to x_t − α h_t; reason: for nonempty compact convex K the nearest point is unique
--   - encoding: finite sequences x_0, …, x_T and h_0, …, h_{T−1} → sequences ℕ → ℝ^m constrained only at t ≤ T and t < T; reason: values beyond the range are never used
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 17, Corollary 4.13

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Subgradient

namespace SubexpPermanent.Main

/-- Corollary 4.13 (averaging with approximate directions), p. 17. -/
theorem corollary_4_13 {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKc : IsCompact K) (hKcv : Convex ℝ K) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ K)
    (T : ℕ) (hT : 1 ≤ T) (α : ℝ) (hα : 0 < α) (G r : ℝ) (hG : 0 ≤ G) (hr : 0 ≤ r)
    (x h : ℕ → EuclideanSpace ℝ (Fin m)) (hxK : ∀ t ≤ T, x t ∈ K)
    (hstep : ∀ t < T,
      ‖h t‖ ≤ G ∧
      f (x t) + inner ℝ (h t) (z - x t) - r ≤ f z ∧
      IsEuclidProj K (x t - α • h t) (x (t + 1))) :
    f ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t) - f z ≤
      ‖x 0 - z‖ ^ 2 / (2 * α * T) + α * G ^ 2 / 2 + r := by sorry

end SubexpPermanent.Main
