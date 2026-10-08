-- Prove2me | Theorems.Thm_PowerTwoChoices_Limit_lemma_2
-- name    : PowerTwoChoices.Limit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:08.241264+00:00
-- url     : https://prove2.me/theorems/f9c9175c-27b6-48b7-a293-435c096e72e3
-- title:
--   Lemma 2 — the unique fixed point of the limiting system with finite mass is $\pi_i=\lambda^{(d^i-1)/(d-1)}$
-- statement:
--   Let $d\ge2$ and $0<\lambda<1$, and consider the limiting supermarket system
--   $$\frac{ds_i}{dt}=\lambda\,(s_{i-1}^d-s_i^d)-(s_i-s_{i+1})\quad(i\ge1),\qquad s_0=1,$$
--   whose states are sequences $s=(s_0,s_1,\dots)$ with $s_0=1$, $s_i\ge0$ and $s_i$ nonincreasing in $i$. A fixed point is a state at which $ds_i/dt=0$ for every $i\ge1$.
--
--   The sequence $\pi_i=\lambda^{(d^i-1)/(d-1)}$ is a state, is a fixed point, and satisfies $\sum_{i\ge1}\pi_i<\infty$; and every fixed point $s$ with
--   $$\sum_{i=1}^\infty s_i<\infty$$
--   equals $\pi$.
--
--   The summability condition cannot be dropped: $(1,1,\dots)$ is also a fixed point. Lemma 2 identifies the point to which the system is later shown to converge, and its doubly exponential decay is the source of the paper's main results.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1097, Lemma 2

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology

namespace PowerTwoChoices.Limit

/-- Lemma 2 (Mitzenmacher 2001, p. 1097). For `d ≥ 2` and `0 < λ < 1`, the limiting system (1)
has a unique fixed point with `∑_{i ≥ 1} s_i < ∞`, namely `π_i = λ^{(d^i-1)/(d-1)}`:
`π` is a state at which every drift `ds_i/dt` (`i ≥ 1`) vanishes and whose tails are summable,
and every state with these two properties equals `π`. -/
theorem lemma_2 (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    IsState (fixedPoint lam d) ∧
    (∀ i : ℕ, 1 ≤ i → drift lam d (fixedPoint lam d) i = 0) ∧
    Summable (fixedPoint lam d) ∧
    ∀ x : ℕ → ℝ, IsState x → (∀ i : ℕ, 1 ≤ i → drift lam d x i = 0) → Summable x →
      x = fixedPoint lam d := by sorry

end PowerTwoChoices.Limit
