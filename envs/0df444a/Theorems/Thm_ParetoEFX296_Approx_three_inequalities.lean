-- Prove2me | Theorems.Thm_ParetoEFX296_Approx_three_inequalities
-- name    : ParetoEFX296.Approx.three_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:42.064362+00:00
-- url     : https://prove2.me/theorems/5e188258-51fa-41a7-bed1-80779e5be7f7
-- title:
--   Proof of Theorem 2 — three strict inequalities
-- statement:
--   Let $K\ge6$ be an integer and $\alpha>2/3+1/K$ be real. Then
--   $$2K+3<\alpha(3K),\qquad K+5<\alpha(2K+2),\qquad K+4<\alpha(2K).$$
--   These are the three strict numerical comparisons used throughout the argument. The first is equality at the excluded threshold; the third is also tight there when $K=6$.
--
--   Differences from the source:
--   - encoding: integer K ≥ 6 and real arithmetic → K : ℕ with 6 ≤ K and explicit real casts in every inequality; reason: natural numbers ≥ 6 represent exactly the source integers ≥ 6; division is real
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.9, Proof of Theorem 2, three inequalities; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Instance

namespace ParetoEFX296.Approx

theorem three_inequalities (K : ℕ) (hK : 6 ≤ K) (α : ℝ) (hα : (2 : ℝ) / 3 + 1 / (K : ℝ) < α) :
    2 * (K : ℝ) + 3 < α * (3 * (K : ℝ)) ∧
    (K : ℝ) + 5 < α * (2 * (K : ℝ) + 2) ∧
    (K : ℝ) + 4 < α * (2 * (K : ℝ)) := by sorry

end ParetoEFX296.Approx
