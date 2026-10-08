-- Prove2me | Theorems.Thm_ShockWear_Inherit_density_deriv_lower
-- name    : ShockWear.Inherit.density_deriv_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:04.729203+00:00
-- url     : https://prove2.me/theorems/65046e84-43ee-405d-bea3-c018ea5b0f6a
-- title:
--   Proof of (3.1) — lower bound on the density derivative
-- statement:
--   In the Poisson shock model with rate $\lambda>0$ and probabilities $1\geq\bar P_0\geq\bar P_1\geq\cdots\geq0$, let $h$ be the positive-time density (2.3). For every $t>0$, the derivative $h'(t)$ exists and satisfies
--
--   $$h'(t)\geq-\lambda h(t).$$
--
--   This is the derivative estimate explicitly invoked in the paper's sign-change argument for the PF₂ density result.
--
--   **Formalization Note** The PF₂ hypothesis of Theorem 3.1(3.1) is not needed for this estimate; nonnegative failure probabilities from the standing shock-model assumptions suffice.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 633, proof of (3.1), derivative estimate following (2.3); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit

/-- The derivative estimate in the proof of (3.1), p. 633. -/
theorem density_deriv_lower (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) :
    ∀ t, 0 < t → ∃ d, HasDerivAt (shockDens lam P) d t ∧
      -(lam * shockDens lam P t) ≤ d := by sorry

end ShockWear.Inherit
