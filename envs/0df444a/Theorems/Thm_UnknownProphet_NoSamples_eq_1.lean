-- Prove2me | Theorems.Thm_UnknownProphet_NoSamples_eq_1
-- name    : UnknownProphet.NoSamples.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:56.91603+00:00
-- url     : https://prove2.me/theorems/47038a4d-df47-443a-971c-f5764ac1fff6
-- title:
--   Equation (1), p. 7 — expected maximum on the hard instance
-- statement:
--   Let $n\ge1$, and let $F$ be the hard distribution with $n^3$ distinct small atoms $v_j$ and the top atom $u$. If $M_n$ is the maximum of $n$ independent draws, then
--
--   $$
--   \mathbb E[M_n]\ge u\Pr(M_n=u),\qquad
--   \Pr(M_n=u)=1-(1-n^{-2})^n\ge\frac{1-1/(2n)}{n}.
--   $$
--
--   This gives the lower bound on the prophet's benchmark used in the main upper bound.
--
--   **Formalization Note** The final inequality is an explicit finite-$n$ replacement for the paper's $(1-o(1))/n$. Draws may repeat; only the atoms themselves are distinct. Division is guarded by $n\ge1$.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 7, proof of Theorem 2, equation (1)

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples

/-- Equation (1), p. 7, with an explicit finite-`n` version of `1-o(1)`. -/
theorem eq_1 (n : ℕ) (hn : 1 ≤ n) (F : FinDist)
    (v : Fin (n ^ 3) → ℝ) (u : ℝ) (hF : IsHardInstance n F v u) :
    probMaxEq F n u * u ≤ expMax F n ∧
      probMaxEq F n u = 1 - (1 - 1 / (n : ℝ) ^ 2) ^ n ∧
      (1 - 1 / (2 * (n : ℝ))) / n ≤ probMaxEq F n u := by sorry

end UnknownProphet.NoSamples
