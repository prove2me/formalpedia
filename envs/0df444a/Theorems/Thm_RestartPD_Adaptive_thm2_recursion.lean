-- Prove2me | Theorems.Thm_RestartPD_Adaptive_thm2_recursion
-- name    : RestartPD.Adaptive.thm2_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:00.524002+00:00
-- url     : https://prove2.me/theorems/e3e5aeda-f9eb-45b6-8496-4af29ecb67b1
-- title:
--   Proof of Theorem 2(ii) — normalized gaps contract across restarts
-- statement:
--   In any adaptive run with $\beta>0$, the restart condition (30) contracts the normalized gap at each successive outer start. In particular, for every $k\ge1$,
--   $$
--   \rho_{\|z^{k,0}-z^{k-1,0}\|_p}(z^{k,0})
--   \le\beta^{k-1}\rho_{\|z^{1,0}-z^{0,0}\|_p}(z^{1,0}).
--   $$
--
--   This is the repeated restart inequality used in the proof of Theorem 2(ii).
--
--   **Formalization Note** This isolated inequality uses the run relation and $\beta>0$; it does not require sharpness or Property 3.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 18, proof of Theorem 2(ii), second inequality

import Mathlib
import Definitions.Def_RestartPD_Adaptive_Restarts

namespace RestartPD.Adaptive

/-- The repeated use of (30) in the second display of the proof of Theorem 2, p. 18. -/
theorem thm2_recursion {n m : ℕ}
    (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ) (X : Set (RestartPD.Fixed.Primal n))
    (Y : Set (RestartPD.Fixed.Dual m)) (p : Seminorm ℝ (RestartPD.Fixed.E n m))
    (Runs : RestartPD.Fixed.E n m → Set (ℕ → RestartPD.Fixed.E n m))
    (β : ℝ) (hβ : 0 < β)
    (τ : ℕ → ℕ) (z : ℕ → RestartPD.Fixed.E n m) (zb : ℕ → ℕ → RestartPD.Fixed.E n m)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb) :
    ∀ k : ℕ, 1 ≤ k →
      RestartPD.Fixed.rho L X Y p (p (z k - z (k - 1))) (z k) ≤
        (((β ^ (k - 1) : ℝ) : ℝ) : EReal) *
          RestartPD.Fixed.rho L X Y p (p (z 1 - z 0)) (z 1) := by sorry

end RestartPD.Adaptive
