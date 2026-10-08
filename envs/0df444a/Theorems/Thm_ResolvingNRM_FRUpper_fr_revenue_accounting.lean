-- Prove2me | Theorems.Thm_ResolvingNRM_FRUpper_fr_revenue_accounting
-- name    : ResolvingNRM.FRUpper.fr_revenue_accounting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:44:06.900971+00:00
-- url     : https://prove2.me/theorems/38b8bfb4-e824-4594-87d0-c490f8666984
-- title:
--   Eq. (32) — v^FR ≥ E[Σ_t Σ_j r_j x_j(t)] − Σ_j r_j (log T + 1) − Σ_j r_j λ_j
-- statement:
--   Consider the network revenue management model with Poisson rates $\lambda_j > 0$, revenues $r_j \ge 0$, nonnegative consumption matrix $A$, initial capacity $C \ge 0$, and an integer horizon $T \ge 1$. Run the Frequent Re-solving policy FR (Algorithm 2) with any optimal-solution selector: at the start of period $t \in \{0, \dots, T-1\}$ it solves the DLP with right-hand side $b(t) = C(t)/(T - t)$, obtains $x(t)$, and accepts class-$j$ arrivals in $[t, t+1)$ with probability $x_j(t)/\lambda_j$ subject to the capacity check. Then the expected revenue of FR satisfies
--   $$v^{\mathrm{FR}} \ \ge\ \mathbb{E}\Big[ \sum_{t=0}^{T-1} \sum_{j=1}^n r_j x_j(t) \Big] - \sum_{j=1}^n r_j (\log T + 1) - \sum_{j=1}^n r_j \lambda_j .$$
--   Since $v^{\mathrm{DLP}} = T \sum_j r_j x^*_j$, this is equivalent to eq. (32):
--   $$v^{\mathrm{DLP}} - v^{\mathrm{FR}} \le T \sum_{j=1}^n r_j x^*_j - \mathbb{E}\Big[ \sum_{t=0}^{T-1} \sum_{j=1}^n r_j x_j(t) \Big] + \sum_{j=1}^n r_j (\log T + 1) + \sum_{j=1}^n r_j \lambda_j .$$
--
--   The inequality separates the revenue FR would earn if its LP targets were met exactly from the losses caused by the capacity check, which are logarithmic in $T$. It reduces Proposition 3 to a comparison of LP values.
--
--   **Formalization Note.** $\log$ is the natural logarithm. $\mathbb{E}[\sum_t \sum_j r_j x_j(t)]$ is written as $\sum_{t=0}^{T-1} \mathbb{E}[r^\top \mathrm{sel}(C(t)/(T-t))]$ with `frStateExp`. The statement is the display at the foot of p. 34, which the paper rewrites as (32) by adding $v^{\mathrm{DLP}} = T\sum_j r_j x_j^*$ to both sides. $\lambda_j > 0$, $r \ge 0$, $a_{lj} \ge 0$, $C \ge 0$ are the model's standing assumptions (p. 7).
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, App. C.2, display at the foot of p. 34 and eq. (32), p. 35

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.FRUpper

/-- Eq. (32), App. C.2, pp. 34–35, in the form of the display at the foot of p. 34:
`v^FR ≥ E[∑_{t=0}^{T-1} ∑_j r_j x_j(t)] − ∑_j r_j (log T + 1) − ∑_j r_j λ_j`, where
`x(t) = sel (b(t))` and `b(t) = C(t) / (T − t)` along FR. -/
theorem fr_revenue_accounting {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel)
    (T : ℕ) (hT : 1 ≤ T) (C : Fin m → ℝ) (hC : 0 ≤ C) :
    (∑ t ∈ Finset.range T,
        frStateExp A r lam sel T t
          (fun c => r ⬝ᵥ sel (fun l => c l / ((T : ℝ) - t))) C)
      - (∑ j, r j) * (Real.log T + 1) - ∑ j, r j * lam j
      ≤ frValue A r lam sel T C := by sorry

end ResolvingNRM.FRUpper
