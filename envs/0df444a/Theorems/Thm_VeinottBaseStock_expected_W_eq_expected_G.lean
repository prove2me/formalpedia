-- Prove2me | Theorems.Thm_VeinottBaseStock_expected_W_eq_expected_G
-- name    : VeinottBaseStock.expected_W_eq_expected_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:42:56.923204+00:00
-- url     : https://prove2.me/theorems/fa014e59-b5d3-4c46-a6ec-bd1904be295e
-- title:
--   §2, p. 210 — $E W_i(y_i, D_i) = E G_i(y_i)$ by independence of $y_i$ and $D_i$
-- statement:
--   Consider the inventory model under its standing assumptions, with independent demands $D_1, D_2, \dots$, $D_i$ having law $\Phi_i$ and values in $\mathfrak{D}_i$. Let $\bar Y$ be a feasible policy and $y_i$ the (random) inventory after ordering in period $i$, which depends only on $D_1, \dots, D_{i-1}$. If $W_i(y_i, D_i)$ is integrable, then
--   $$E\, W_i(y_i, D_i) = E\, G_i(y_i).$$
--
--   This is the identity that turns the expected discounted cost (2.2) into the form (2.3), and hence (2.4), in terms of the one-period functions $G_i$; it is the only place where the independence of the demands is used.
--
--   **Formalization Note.** Lean period $k$ is the paper's period $k+1$. The integrability of $W_i(y_i, D_i)$ is used by the paper without being stated (the expectation $E W_i(y_i, D_i)$ is taken as existing); it is added as the hypothesis `hint`.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 210, §2 (derivation of (2.3))

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- §2, p. 210: for a feasible policy, `y_i` depends only on `D_1, …, D_{i-1}`, which are
independent of `D_i`, so `E W_i(y_i, D_i) = E G_i(y_i)` (when the left side exists). -/
theorem expected_W_eq_expected_G {n m : ℕ} (M : Model n m) (x₁ : Fin n → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → Fin m → ℝ) (hM : M.Standing) (hD : M.IsDemandProcess P D)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (k : ℕ)
    (hint : Integrable (fun ω => M.W k (M.orderSeq Ŷ (fun j => D j ω) k) (D k ω)) P) :
    ∫ ω, M.W k (M.orderSeq Ŷ (fun j => D j ω) k) (D k ω) ∂P =
      ∫ ω, M.G k (M.orderSeq Ŷ (fun j => D j ω) k) ∂P := by sorry

end VeinottBaseStock
