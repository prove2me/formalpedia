-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_lemma_22
-- name    : QuadMemory.ConvexOpt.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:57.911173+00:00
-- url     : https://prove2.me/theorems/a02a55f3-0891-46c5-a5ab-c714d934689e
-- title:
--   Lemma 22, p. 37 — r robustly independent unit vectors yield ⌈r/s⌉ orthonormal vectors with ‖Zᵀa‖_∞ ≤ (√d/δ)^{s/(s−1)}‖Yᵀa‖_∞
-- statement:
--   Let $\delta\in(0,1]$ and let $y_1,\dots,y_r\in\mathbb R^d$ be $r\le d$ unit vectors such that, for every $i\le r$,
--   $$\|P_{\mathrm{Span}(y_j,\,j<i)^\perp}(y_i)\|\ge\delta .$$
--   Let $Y=[y_1,\dots,y_r]$ and $s\ge2$. Then there are $\lceil r/s\rceil$ orthonormal vectors $Z=[z_1,\dots,z_{\lceil r/s\rceil}]$ such that for every $a\in\mathbb R^d$,
--   $$\|Z^\top a\|_\infty\le\Big(\frac{\sqrt d}\delta\Big)^{s/(s-1)}\|Y^\top a\|_\infty .$$
--
--   Applied to the winning vectors of Game 2 with $a$ a row of $A$, it turns robustly independent, nearly $A$-orthogonal vectors into orthonormal ones, the form in which Lemma 12 applies.
--
--   **Formalization Note.** The page's hypothesis reads "for any $i\le k$", where $k$ is not bound in the lemma; it is read as $i\le r$. $s$ is real. $\|P_{W^\perp}(y)\|$ is the distance from $y$ to $W$, as in the winning condition of Game 2. For $r=0$ both sides are $0$.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 37, Lemma 22 (proof p. 38)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

open scoped RealInnerProductSpace

namespace QuadMemory.ConvexOpt

/-- Lemma 22 (p. 37): let `δ ∈ (0, 1]` and let `y_1, …, y_r` (`r ≤ d`) be unit vectors of `ℝ^d`
with `‖P_{Span(y_j, j<i)^⊥}(y_i)‖ ≥ δ` for every `i ≤ r`. For every `s ≥ 2` there are `⌈r/s⌉`
orthonormal vectors `z_1, …, z_{⌈r/s⌉}` such that for every `a ∈ ℝ^d`,
`‖Zᵀa‖_∞ ≤ (√d/δ)^{s/(s-1)} ‖Yᵀa‖_∞`. -/
theorem lemma_22 (d r : ℕ) (hr : r ≤ d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ys : Fin r → E d) (hys : ∀ i, ‖ys i‖ = 1) (hperp : ∀ i, δ ≤ perpNorm ys i)
    (s : ℝ) (hs : 2 ≤ s) :
    ∃ Z : Fin ⌈(r : ℝ) / s⌉₊ → E d, Orthonormal ℝ Z ∧
      ∀ a : E d, (⨆ i, |⟪Z i, a⟫|) ≤
        (Real.sqrt d / δ) ^ (s / (s - 1)) * ⨆ j, |⟪ys j, a⟫| := by sorry

end QuadMemory.ConvexOpt
