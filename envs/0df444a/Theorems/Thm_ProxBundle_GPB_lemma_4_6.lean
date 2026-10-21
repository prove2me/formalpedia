-- Prove2me | Theorems.Thm_ProxBundle_GPB_lemma_4_6
-- name    : ProxBundle.GPB.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:22.518054+00:00
-- url     : https://prove2.me/theorems/2b08c878-7e63-4918-afea-a062e11eaac4
-- title:
--   Lemma 4.6, p. 16 — contraction on null iterations
-- statement:
--   For any GPB run satisfying the hybrid condition with pair $(\bar M_f,\bar L_f)$ and the input condition (29), every null iteration $j\ge1$ obeys
--   $$
--   t_{j+1}-\frac{\bar\varepsilon}{4}\le\tau\left(t_j-\frac{\bar\varepsilon}{4}\right).
--   $$
--   Thus the shifted model gap contracts along consecutive null steps. This is the cycle-length estimate's recurrence.
--
--   **Formalization Note** A null index is one with $t_j>\bar\varepsilon/2$; the run retains the full existential BU condition.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 16, Lemma 4.6, (55)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Lemma 4.6, p. 16: contraction (55) on a null iteration. -/
theorem lemma_4_6 {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hrun : IsRun P μ lam ε τ x0 R)
    (j : ℕ) (hj : 1 ≤ j) (hnull : ε / 2 < R.t P lam j) :
    R.t P lam (j + 1) - ε / 4 ≤ τ * (R.t P lam j - ε / 4) := by sorry

end ProxBundle.GPB
