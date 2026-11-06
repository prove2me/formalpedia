-- Prove2me | Theorems.Thm_SilverRateLB_lemma_3_2
-- name    : SilverRateLB.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:25.925105+00:00
-- url     : https://prove2.me/theorems/5db09f0e-fd1f-44a8-a190-03e5a883867e
-- title:
--   Lemma 3.2 — local hard function for one gap
-- statement:
--   Let $\varepsilon,\gamma>0$ and let $a,c$ be the constants of Lemma 2.4. Let $m\ge0$, $h_1,\dots,h_m\ge0$, $s=\sum_{j=1}^mh_j$ and $b>2$. There exist a nonnegative convex $1$-smooth $f:\mathbb R^2\to\mathbb R$ and a threshold $\tau>0$ with
--   $$f(x,y)=0\ \ (x\le0,\ y\ge0),\qquad \partial_2f(x,y)=0\ \ (x\in\mathbb R,\ y\ge\tau),\tag{8}$$
--   such that gradient descent on $f/2$ from $(x_0,y_0)=(1,0)$ with stepsizes $h_1,\dots,h_m,b$ satisfies
--   $$x_j>0,\quad 0\le y_j\le y_m=\tau-\frac{2}{c(a+s)}\quad(0\le j\le m),\qquad y_{m+1}=\tau+\frac{b-2}{c(a+s)}.$$
--
--   During the gap the second coordinate stays below $\tau$; the checkpoint step leaves the excess $(b-2)/(c(a+s))$, which becomes the transfer ratio $D_{i+1}/D_i$ of the chain.
--
--   Differences from the source:
--   - encoding: the list of properties of (f, τ) → IsLocalHard (aOf ε γ) (cOf ε γ) hs b f τ; reason: the definition lists exactly the lemma's conclusions
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma 3.2, p. 12

import Mathlib
import Definitions.Def_SilverRateLB_aOf
import Definitions.Def_SilverRateLB_IsLocalHard

namespace SilverRateLB

/-- **Lemma 3.2 (local hard function).** Let `ε, γ > 0`, `m ≥ 0`, `h_1, …, h_m ≥ 0`,
`s = ∑ h_j` and `b > 2`. There exist a nonnegative convex `1`-smooth `f : ℝ² → ℝ` and a threshold
`τ > 0` with `f(x, y) = 0` (`x ≤ 0, y ≥ 0`) and `∂₂f(x, y) = 0` (`x ∈ ℝ, y ≥ τ`) (8), such that GD on
`f/2` from `(1, 0)` with stepsizes `h_1, …, h_m, b` satisfies `x_j > 0`,
`0 ≤ y_j ≤ y_m = τ − 2/(c(a+s))` (`0 ≤ j ≤ m`) and `y_{m+1} = τ + (b−2)/(c(a+s))`, where `a`, `c`
are the constants of Lemma 2.4.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma 3.2, p. 12 (proof §A.2, pp. 24–25).

**Formalization Note** The conclusion is bundled as `IsLocalHard (aOf ε γ) (cOf ε γ) hs b f τ`;
`hs` is the list `(h_1, …, h_m)`, possibly empty. -/
theorem lemma_3_2 (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    (b : ℝ) (hb : 2 < b) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (τ : ℝ), IsLocalHard (aOf ε γ) (cOf ε γ) hs b f τ := by sorry

end SilverRateLB
