-- Prove2me | Theorems.Thm_ProxBundle_GPB_lemma_A_3
-- name    : ProxBundle.GPB.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:46.084437+00:00
-- url     : https://prove2.me/theorems/24d3ae89-aa7c-4294-9745-93aeeccc349b
-- title:
--   Lemma A.3, p. 25 — displacement after a serious step
-- statement:
--   Let $j$ be a serious iteration of a GPB run, before its first $\bar\varepsilon$-solution, and let $d_0$ be the distance of $x_0$ from the solution set. For the minimizing hybrid pair $(\bar M_f,\bar L_f)$,
--   $$
--   \|x_j-x_{j+1}\|\le2\sqrt2\left(\max\{1,2\lambda\bar L_f\}d_0+\lambda\bar M_f\right).
--   $$
--   This bounds the step that follows a serious update and feeds the initial-gap estimate for each cycle.
--
--   **Formalization Note** The pre-solution condition is needed by the printed proof's use of (48). The theorem accepts any nonnegative pair satisfying (A3), a strengthening of the paper's minimizing-pair choice.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 25, Lemma A.3, (74)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Lemma A.3, p. 25: a serious step before the first ε-solution. -/
theorem lemma_A_3 {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hopt : P.IsNearestOpt x0 x0s)
    (hrun : IsRun P μ lam ε τ x0 R)
    (j : ℕ) (hserious : R.t P lam j ≤ ε / 2)
    (hbefore : j = 0 ∨ ε < P.φ (R.y j) - P.φ x0s) :
    ‖R.x j - R.x (j + 1)‖ ≤
      2 * Real.sqrt 2 *
        (max 1 (2 * lam * Lbar) * ‖x0 - x0s‖ + lam * Mbar) := by sorry

end ProxBundle.GPB
