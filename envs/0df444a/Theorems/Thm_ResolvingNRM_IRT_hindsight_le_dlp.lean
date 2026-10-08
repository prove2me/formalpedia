-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_hindsight_le_dlp
-- name    : ResolvingNRM.IRT.hindsight_le_dlp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:20:46.493655+00:00
-- url     : https://prove2.me/theorems/be92f966-67a4-4107-9583-98a6910d3564
-- title:
--   Sec. 2.2.2, p. 9 — the hindsight optimum is at most the DLP value: $v^{\mathrm{HO}} \le v^{\mathrm{DLP}}$
-- statement:
--   Consider the network revenue-management model with $n$ classes of Poisson rates $\lambda_j > 0$, revenues $r_j \ge 0$ and a nonnegative bill-of-materials matrix $A \in \mathbb R^{m\times n}$. For every horizon $T > 0$ and every capacity vector $C \ge 0$, the hindsight optimum is bounded by the value of the deterministic LP:
--   $$v^{\mathrm{HO}}(T, C) = \mathbb E\big[V^{\mathrm{HO}}\big] \;\le\; v^{\mathrm{DLP}}(T, C) = T\max\Big\{\sum_j r_j x_j \ \Big|\ \sum_j A_j x_j \le C/T,\ 0 \le x_j \le \lambda_j\Big\}.$$
--
--   Together with $v^* \le v^{\mathrm{HO}}$ this makes the hindsight optimum a tighter upper bound than the DLP; it is what turns Proposition 5's bound against the DLP into a bound on the regret against the hindsight optimum.
--
--   **Formalization Note** Only the second inequality of the display $v^* \le v^{\mathrm{HO}} \le v^{\mathrm{DLP}}$ is stated: the optimal value $v^*$ over all admissible policies is not defined in this mission. The positivity of the rates and the nonnegativity of $r$ and $A$ are the standing assumptions of Sec. 2, p. 7, which the page leaves implicit. The horizon $T$ is real.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Sec. 2.2.2, p. 9, display 'v* ≤ v^HO ≤ v^DLP'

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem hindsight_le_dlp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j)
    (T : ℝ) (hT : 0 < T) (C : Fin m → ℝ) (hC : 0 ≤ C) :
    hindsightValue A r lam T C ≤ dlpValue A r lam T C := by sorry

end ResolvingNRM.IRT
