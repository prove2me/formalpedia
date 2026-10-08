-- Prove2me | Theorems.Thm_Pegasos_Analysis_eq_10
-- name    : Pegasos.Analysis.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:06.682293+00:00
-- url     : https://prove2.me/theorems/2b6ea2a2-7386-4fe6-b351-e31ffdb72df3
-- title:
--   Eq. (10) — the sub-gradient inequality for λ-strongly convex functions
-- statement:
--   Call $f:\mathbb R^n\to\mathbb R$ **$\lambda$-strongly convex** if $w \mapsto f(w) - \frac\lambda2\|w\|^2$ is convex, and call $g$ a **sub-gradient** of $f$ at $w$ if $f(u) - f(w) \ge \langle g, u - w\rangle$ for every $u$.
--
--   If $f$ is $\lambda$-strongly convex and $g$ is a sub-gradient of $f$ at $w$, then for every $u \in \mathbb R^n$
--   $$\langle w - u, g\rangle \;\ge\; f(w) - f(u) + \frac{\lambda}{2}\|w - u\|^2 .$$
--
--   This is the per-round inequality that, in the proof of Lemma 1, upgrades the linear lower bound of a sub-gradient to a quadratic one; it is what produces the logarithmic rate.
--
--   **Formalization Note.** Strong convexity is stated as the paper defines it (p. 9), as convexity of $f - \frac\lambda2\|\cdot\|^2$ on all of $\mathbb R^n$; no sign condition on $\lambda$ is imposed, since the inequality holds for every real $\lambda$. No differentiability is assumed.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 10, Eq. (10) (proof of Lemma 1); λ-strong convexity p. 9; sub-gradient p. 17

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Eq. (10)** (p. 10, proof of Lemma 1): if `f` is λ-strongly convex in the paper's sense
(`f(w) − λ/2‖w‖²` is convex, p. 9) and `g` is a sub-gradient of `f` at `w`
(`∀ u, f(u) − f(w) ≥ ⟨g, u − w⟩`, p. 17), then for every `u`,
`⟨w − u, g⟩ ≥ f(w) − f(u) + λ/2 ‖w − u‖²`. -/
theorem eq_10 {n : ℕ} (lam : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ (fun v => f v - lam / 2 * ‖v‖ ^ 2))
    (w g : EuclideanSpace ℝ (Fin n)) (hg : UnderstandingML.IsSubgradient f w g)
    (u : EuclideanSpace ℝ (Fin n)) :
    f w - f u + lam / 2 * ‖w - u‖ ^ 2 ≤ inner ℝ (w - u) g := by sorry

end Pegasos.Analysis
