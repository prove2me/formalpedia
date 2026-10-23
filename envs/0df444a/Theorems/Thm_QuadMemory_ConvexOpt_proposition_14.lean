-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_proposition_14
-- name    : QuadMemory.ConvexOpt.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:51.025617+00:00
-- url     : https://prove2.me/theorems/a5085a77-6ecc-45db-b8f6-307852876058
-- title:
--   Proposition 14, p. 23 — a Player winning Game 2 with probability ≥ 1/2 makes m ≥ c_H d/(8(30 log d + c_H)) queries
-- statement:
--   Let $c_H>0$ be a constant for which Lemma 12 holds, and $n=\lceil d/4\rceil$. Let
--   $$k\ge20\,\frac{M+3d\log(2d)+1}{c_Hn},$$
--   and let $0<\alpha,\beta\le1$ satisfy $\alpha(\sqrt d/\beta)^{5/4}\le\frac12$. If the Player wins the Orthogonal Vector Game with Hints (Game 2) with parameters $(d,k,m,M,\alpha,\beta)$ with probability at least $1/2$, then
--   $$m\ge\frac{c_H}{8(30\log d+c_H)}\,d .$$
--
--   This is the memory–query trade-off for the game: with $M$ bits of message, $k\approx M/d$ near-kernel directions must be found, and that costs $\tilde\Omega(d)$ queries in the second phase. It holds for every discretization $\mathcal D_\delta$.
--
--   **Formalization Note.** Logarithms are base 2 here, as the proof counts bits ("$md$ bits", "$d^{-4}\log e$"). The text layer of the PDF drops the factor $20$ in the hypothesis on $k$; the rendered page has it. The win probability is the finite-sum law of the Game module.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 23, Proposition 14 (proof pp. 23–25)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

namespace QuadMemory.ConvexOpt

/-- Proposition 14 (p. 23): let `c_H > 0` be a constant of Lemma 12, `n = ⌈d/4⌉`,
`k ≥ 20 (M + 3 d log(2d) + 1)/(c_H n)` and `0 < α, β ≤ 1` with `α (√d/β)^{5/4} ≤ 1/2`. If the
Player wins Game 2 with parameters `(d, k, m, M, α, β)` with probability at least `1/2`, then
`m ≥ c_H d / (8 (30 log d + c_H))`. Logarithms are in base 2. -/
theorem proposition_14 (cH : ℝ) (hcH : 0 < cH) (hH : IsHypercubeConst cH)
    (d k m M : ℕ)
    (hk : 20 * ((M : ℝ) + 3 * d * Real.logb 2 (2 * d) + 1) / (cH * nRows d) ≤ k)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hαβ : α * (Real.sqrt d / β) ^ ((5 : ℝ) / 4) ≤ 1 / 2)
    (D : SphereDisc d) (P : Player d k m M D) (hwin : 1 / 2 ≤ winProb P α β) :
    cH / (8 * (30 * Real.logb 2 d + cH)) * d ≤ m := by sorry

end QuadMemory.ConvexOpt
