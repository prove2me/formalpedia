-- Prove2me | Theorems.Thm_ProxBundle_GPB_lemma_4_7
-- name    : ProxBundle.GPB.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:23.895667+00:00
-- url     : https://prove2.me/theorems/15820c93-3c25-4167-9bc0-95e645618763
-- title:
--   Lemma 4.7, p. 16 — initial gap of each cycle
-- statement:
--   Let $j$ be a serious index of GPB before its first $\bar\varepsilon$-solution. Put $d_0=\|x_0-x_0^*\|$ and
--   $$
--   \bar t=\bar M_f^2+4(\bar L_f+2)\bigl(\max\{1,2\lambda\bar L_f\}d_0+\lambda\bar M_f\bigr)^2.
--   $$
--   Then the following iteration starts with gap $t_{j+1}\le\bar t$. The bound initializes the null-step contraction in every cycle.
--
--   **Formalization Note** The pre-solution restriction is required by the argument establishing the displacement bound. Any admissible nonnegative hybrid pair can be used in place of the minimizing pair.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 16, Lemma 4.7, (58)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Lemma 4.7, p. 16, with the pre-solution qualification used by its proof. -/
theorem lemma_4_7 {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hopt : P.IsNearestOpt x0 x0s)
    (hrun : IsRun P μ lam ε τ x0 R)
    (j : ℕ) (hserious : R.t P lam j ≤ ε / 2)
    (hbefore : j = 0 ∨ ε < P.φ (R.y j) - P.φ x0s) :
    R.t P lam (j + 1) ≤ tbar Mbar Lbar lam ‖x0 - x0s‖ := by sorry

end ProxBundle.GPB
