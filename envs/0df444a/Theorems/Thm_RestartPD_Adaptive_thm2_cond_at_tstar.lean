-- Prove2me | Theorems.Thm_RestartPD_Adaptive_thm2_cond_at_tstar
-- name    : RestartPD.Adaptive.thm2_cond_at_tstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:01.219736+00:00
-- url     : https://prove2.me/theorems/36fd43f4-3200-4ae2-a187-adc493dd174c
-- title:
--   Proof of (33) — the adaptive test holds at the ceiling time
-- statement:
--   Under Theorem 2's standing primal–dual assumptions, Property 3, and $\alpha$-sharpness on a set $S$ containing every outer start, let $\beta\in(0,1)$ and let the run use the adaptive rule (30). Set
--   $$
--   t^\star=\left\lceil\frac{2C(q+2)}{\alpha\beta}\right\rceil.
--   $$
--   For each outer index $k\ge1$, the restart inequality (30) holds at inner time $t^\star$:
--   $$
--   \rho_{\|\bar z^{k,t^\star}-z^{k,0}\|_p}(\bar z^{k,t^\star})
--   \le\beta\rho_{\|z^{k,0}-z^{k-1,0}\|_p}(z^{k,0}).
--   $$
--
--   This is the displayed comparison in the proof of the uniform restart-length bound.
--
--   **Formalization Note** The statement includes zero seminorm displacement; in that case the right-limsup definition of $\rho_0$ applies.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 18, proof of Theorem 2, display proving (33)

import Mathlib
import Definitions.Def_RestartPD_Adaptive_Restarts

namespace RestartPD.Adaptive

/-- The condition reached at the ceiling time in the proof of (33), p. 18. -/
theorem thm2_cond_at_tstar {n m : ℕ}
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
    ∀ k : ℕ, 1 ≤ k → RestartCond L X Y p β z zb k tstar := by sorry

end RestartPD.Adaptive
