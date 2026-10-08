-- Prove2me | Theorems.Thm_Pegasos_Analysis_lemma_1
-- name    : Pegasos.Analysis.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:04.83003+00:00
-- url     : https://prove2.me/theorems/0777f68b-0b38-45a8-8dc2-cd1b681ddf2f
-- title:
--   Lemma 1 — projected sub-gradient steps 1/(λt) on λ-strongly convex functions have average regret G²(1+ln T)/(2λT)
-- statement:
--   Let $\lambda > 0$, let $f_1,\dots,f_T:\mathbb R^n\to\mathbb R$ be $\lambda$-strongly convex (each $f_t - \frac\lambda2\|\cdot\|^2$ is convex), and let $B\subseteq\mathbb R^n$ be closed and convex, with Euclidean projection $\Pi_B(w) = \arg\min_{w'\in B}\|w - w'\|$. Let $w_1,\dots,w_{T+1}$ satisfy $w_1\in B$ and, for $1\le t\le T$,
--   $$w_{t+1} = \Pi_B(w_t - \eta_t\nabla_t),\qquad \eta_t = \frac{1}{\lambda t},$$
--   where $\nabla_t$ is a sub-gradient of $f_t$ at $w_t$ with $\|\nabla_t\|\le G$. Then for every $u\in B$,
--   $$\frac1T\sum_{t=1}^T f_t(w_t) \;\le\; \frac1T\sum_{t=1}^T f_t(u) + \frac{G^2(1+\ln T)}{2\lambda T}.$$
--
--   This is the logarithmic-regret bound for online sub-gradient descent on strongly convex losses, without any smoothness; Theorem 1 is this lemma applied to the Pegasos iterates.
--
--   **Formalization Note.** The step producing $w_{t+1}$ uses $\eta_t = 1/(\lambda t)$, as in the paper (iterations are 1-based). "$w_{t+1}$ is the projection" is the predicate `IsProj B v z` ($z \in B$ and $\|z - v\| \le \|w - v\|$ for all $w\in B$). The hypotheses are required only for $1 \le t \le T$. No lower bound on $T$ is assumed; at $T = 0$ both sides are $0$ in Lean.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 10, Lemma 1

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Lemma 1** (p. 10): let `f₁, …, f_T` be λ-strongly convex (`f_t − λ/2‖·‖²` convex),
`B` a closed convex set, `w₁ ∈ B` and, for `t ≥ 1`, `w_{t+1} = Π_B(w_t − η_t ∇_t)` with
`∇_t` a sub-gradient of `f_t` at `w_t`, `η_t = 1/(λt)` and `‖∇_t‖ ≤ G`. Then for all
`u ∈ B`, `(1/T) Σ_{t=1}^T f_t(w_t) ≤ (1/T) Σ_{t=1}^T f_t(u) + G²(1 + ln T)/(2λT)`. -/
theorem lemma_1 {n : ℕ} (lam G : ℝ) (hlam : 0 < lam) (B : Set (EuclideanSpace ℝ (Fin n)))
    (hBclosed : IsClosed B) (hBconvex : Convex ℝ B) (T : ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (w g : ℕ → EuclideanSpace ℝ (Fin n))
    (hf : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (fun v => f t v - lam / 2 * ‖v‖ ^ 2))
    (hw1 : w 1 ∈ B)
    (hstep : ∀ t ∈ Finset.Icc 1 T,
      LogRegretOCO.OGD.IsProj B (w t - (1 / (lam * (t : ℝ))) • g t) (w (t + 1)))
    (hg : ∀ t ∈ Finset.Icc 1 T, UnderstandingML.IsSubgradient (f t) (w t) (g t))
    (hG : ∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ G)
    (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ B) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, f t (w t)
      ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, f t u
        + G ^ 2 * (1 + Real.log T) / (2 * lam * T) := by sorry

end Pegasos.Analysis
