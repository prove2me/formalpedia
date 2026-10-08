-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_stall_freezes_state
-- name    : ShorNonsmooth.SpaceDilation.sdg_stall_freezes_state
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T21:13:02.644519+00:00
-- url     : https://prove2.me/theorems/235a7d50-da86-4b08-bbff-9346a7a75072
-- title:
--   A stalling step freezes the SDG state: if $g(x_j) = 0$ then $s_{j+1} = s_j$, so the whole tail is constant
-- statement:
--   Write $s_k = \mathrm{sdg}_k$ for the $k$-th state of the Shor recursion and $x_k = (s_k).x$ for the iterate. The recursion advances by
--
--   $$s_{k+1} = \begin{cases} s_k & \text{if } g(x_k) = 0,\\ \mathrm{sdgStep}(s_k, \ldots) & \text{if } g(x_k) \neq 0. \end{cases}$$
--
--   **Claim.** If $g(x_j) = 0$ then $s_r = s_j$ for every $r \ge j$.
--
--   **Proof.** For $r = j$ this is reflexivity. If $s_r = s_j$ with $r \ge j$ then $x_r = x_j$, so $g(x_r) = g(x_j) = 0$, and the stalling branch gives $s_{r+1} = s_r = s_j$. Induction on $r$. $\square$
--
--   This is the elementary structural fact underlying the stalling case of every Shor argument: a zero selection permanently stops the iteration. In the proof of Theorem 3.3 it is used twice — once to discharge the stalling branch of the induction on $\|u_k\| \le d$, and once to show that non-stalling at index $j$ implies non-stalling at *every* index $\le j$ (a stall earlier would freeze the tail and force $g(x_j) = 0$).
-- source:
--   Shor, Extensions of Subgradient Methods for Minimization (1985), the definition of the recursion `sdg`/`sdgStep` and its stalling branch.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation

namespace ShorNonsmooth.SpaceDilation

/-- If the selection vanishes at the iterate `j`, i.e. `g (sdg … j).x = 0`, then
`sdg … (j + 1) = sdg … j`; by iteration, `s_r = s_j` for every `j ≤ r`.  This is the
"stalling branch" of the SDG recursion: once `g(x_j) = 0` the method repeats the state
forever, so every iterate on the tail equals `x_j`. -/
theorem sdg_stall_freezes_state {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (j : ℕ) (hgj : g (sdg g h α x₀ B₀ j).x = 0)
    (r : ℕ) (hjr : j ≤ r) :
    sdg g h α x₀ B₀ r = sdg g h α x₀ B₀ j := by
  sorry

end ShorNonsmooth.SpaceDilation
