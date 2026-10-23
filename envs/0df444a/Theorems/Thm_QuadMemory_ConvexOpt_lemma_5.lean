-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_lemma_5
-- name    : QuadMemory.ConvexOpt.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:01.200471+00:00
-- url     : https://prove2.me/theorems/2fbcdc71-67ef-4b03-b0c9-c9cddd76c0ef
-- title:
--   Lemma 5, p. 8 — the sphere S^{d−1} splits into (O(1)/δ)^d equal-measure cells of diameter at most δ
-- statement:
--   There is an absolute constant $C>0$ with the following property. For every dimension $d\ge1$ and every $0<\delta<\pi/2$, the unit sphere $S^{d-1}\subset\mathbb R^d$ can be partitioned into $N(\delta)$ measurable cells, all of the same uniform measure and each of diameter at most $\delta$, with
--   $$N(\delta)\le\Big(\frac C\delta\Big)^d .$$
--
--   The partition, with a representative in each cell, gives the discretization $\mathcal D_\delta$ and the map $\varphi_\delta$ through which the hard instance reveals its hidden vectors with only $O(d\log(1/\delta))$ bits each.
--
--   **Formalization Note.** The paper cites this from Feige and Schechtman (2002, Lemma 21) without proof. Diameter is Euclidean, which is at most the geodesic diameter; this is what the use of $\varphi_\delta$ needs ($\|\varphi_\delta(y)-y\|\le\delta$).
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 8, Lemma 5 (citing Feige & Schechtman 2002, Lemma 21)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

namespace QuadMemory.ConvexOpt

/-- Lemma 5 (p. 8, from Feige–Schechtman 2002, Lemma 21): there is an absolute constant `C > 0`
such that for every `d ≥ 1` and every `0 < δ < π/2` the sphere `S^{d-1}` can be partitioned into
`N(δ) ≤ (C/δ)^d` cells of equal measure, each of (Euclidean) diameter at most `δ`. -/
theorem lemma_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ δ : ℝ, 0 < δ → δ < Real.pi / 2 →
      ∃ D : SphereDisc d, (Fintype.card D.ι : ℝ) ≤ (C / δ) ^ d ∧ D.DiamLe δ := by sorry

end QuadMemory.ConvexOpt
