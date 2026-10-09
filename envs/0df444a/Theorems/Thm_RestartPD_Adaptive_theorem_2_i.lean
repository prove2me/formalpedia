-- Prove2me | Theorems.Thm_RestartPD_Adaptive_theorem_2_i
-- name    : RestartPD.Adaptive.theorem_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:30.702827+00:00
-- url     : https://prove2.me/theorems/18c6d27a-bdee-4337-a9ce-c1060e80d96e
-- title:
--   Theorem 2(i), (33) — adaptive restart lengths are at most the ceiling time
-- statement:
--   Under Theorem 2's standing primal–dual assumptions, Property 3, and $\alpha$-sharpness on a set $S$ containing every outer start, let $\beta\in(0,1)$ and run Algorithm 1 with the adaptive restart rule. For every outer index $k\ge1$,
--   $$
--   \tau^k\le t^\star=\left\lceil\frac{2C(q+2)}{\alpha\beta}\right\rceil.
--   $$
--
--   This is the uniform cap on the number of inner steps between later restarts. The user-chosen first length $\tau^0$ is outside the claim.
--
--   **Formalization Note** The adaptive run requires $\tau^k$ to be the first positive time meeting (30); an arbitrary later qualifying time would invalidate this bound.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 18, Theorem 2(i), (33)

import Mathlib
import Definitions.Def_RestartPD_Adaptive_Restarts

namespace RestartPD.Adaptive

/-- Theorem 2(i), equation (33), p. 18. -/
theorem theorem_2_i {n m : ℕ}
    (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ) (X : Set (RestartPD.Fixed.Primal n))
    (Y : Set (RestartPD.Fixed.Dual m)) (hP : RestartPD.Fixed.IsPDProblem L X Y)
    (p : Seminorm ℝ (RestartPD.Fixed.E n m)) (Runs : RestartPD.Fixed.E n m → Set (ℕ → RestartPD.Fixed.E n m))
    (q C : ℝ) (h3 : RestartPD.Fixed.Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (τ : ℕ → ℕ) (z : ℕ → RestartPD.Fixed.E n m) (zb : ℕ → ℕ → RestartPD.Fixed.E n m)
    (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (S : Set (RestartPD.Fixed.E n m)) (hzS : ∀ k, z k ∈ S)
    (hsharp : RestartPD.Fixed.IsSharpOn L X Y p α S) :
    let tstar := Nat.ceil (2 * C * (q + 2) / (α * β))
    ∀ k : ℕ, 1 ≤ k → τ k ≤ tstar := by sorry

end RestartPD.Adaptive
