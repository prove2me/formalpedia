-- Prove2me | Theorems.Thm_TwoSidedGrowth_Balance_eq_33
-- name    : TwoSidedGrowth.Balance.eq_33
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:19.178124+00:00
-- url     : https://prove2.me/theorems/d39d9485-67d7-4ccf-9715-da620ce8b781
-- title:
--   (33), p. 43 — the maximizer of G(·, x) over [0, 1] is unique and is the clamped inverse of h′ at (β^s_0 − β^d_0)x^{1−α}/(v − c)
-- statement:
--   In the two-sided growth model under its standing assumptions, let $\kappa(x)=(\beta^s_0-\beta^d_0)x^{1-\alpha}/(v-c)$. For every market size $x>0$:
--   1. exactly one balance $\gamma$ satisfies the clamp formula
--   $$\gamma^*(x)=\max\Bigl\{\min\bigl\{(h')^{-1}(\kappa(x)),1\bigr\},0\Bigr\},\tag{33}$$
--   read with the extended inverse of the strictly decreasing $h'$ on $(0,1)$ (an interior root of $h'(\gamma)=\kappa(x)$, or $0$ when $h'\le\kappa(x)$ throughout $(0,1)$, or $1$ when $\kappa(x)\le h'$ throughout $(0,1)$);
--   2. a balance $\gamma\in[0,1]$ maximizes $G(\cdot,x)$ over $[0,1]$ if and only if it satisfies (33).
--
--   So the formula (33) is precisely the argmax of the net welfare rate over the balance interval.
--
--   **Formalization Note.** The proof on p. 42 asserts that $h'$ is bounded by $h'(0)$ and $h'(1)$; this fails when $h'$ is unbounded at an end (Cobb–Douglas), and the extended inverse is the reading the proof of Theorem 1 (p. 51) uses. $h'$ is never evaluated at $0$ or $1$.
-- source:
--   Lian, van Ryzin, Optimal Growth in Two-Sided Markets, SSRN working paper 3310559 (version of 2020-01-16), p. 43, display (33) in the proof of Lemma 6

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Setting

namespace TwoSidedGrowth.Balance
theorem eq_33 (M : Model) (hM : M.Standing) :
    (∀ x : ℝ, 0 < x → ∃! γ : ℝ, IsBalance M x γ) ∧
    (∀ x : ℝ, 0 < x → ∀ γ ∈ Set.Icc (0:ℝ) 1,
      ((∀ η ∈ Set.Icc (0:ℝ) 1, G M η x ≤ G M γ x) ↔ IsBalance M x γ)) := by sorry
end TwoSidedGrowth.Balance
