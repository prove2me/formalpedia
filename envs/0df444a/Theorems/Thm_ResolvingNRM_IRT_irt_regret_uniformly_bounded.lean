-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_irt_regret_uniformly_bounded
-- name    : ResolvingNRM.IRT.irt_regret_uniformly_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:21:48.112213+00:00
-- url     : https://prove2.me/theorems/bcd79de5-55c0-40d0-b9d8-70530366ccd5
-- title:
--   Theorem 1, p. 16 — the IRT policy has regret $v^{\mathrm{HO}} - v^{\mathrm{IRT}} = O(1)$, uniformly in $T$ and $C$
-- statement:
--   Consider the network revenue-management model with $n$ customer classes arriving as independent Poisson processes of rates $\lambda_j > 0$, revenues $r_j \ge 0$, and $m$ resources consumed according to a nonnegative bill-of-materials matrix $A$. The **Infrequent Re-solving with Thresholding** (IRT) policy (Algorithm 3) re-solves the deterministic LP at the $K = \lceil\log\log T/\log(6/5)\rceil$ times $t^*_u = T - T^{(5/6)^u}$, uses the LP solution, rounded to $0$ or $1$ by the thresholds $\tau_u^{-1/4}$, as acceptance probabilities in every epoch but the last, and the unrounded probabilities $x^K_j/\lambda_j$ in the last epoch.
--
--   There is a constant $M$, depending only on $(\lambda, r, A)$, such that for every choice of optimal LP solutions, every horizon $T \in \{1, 2, \dots\}$ and every capacity vector $C \ge 0$,
--   $$v^{\mathrm{HO}}(T, C) - v^{\mathrm{IRT}}(T, C) \le M .$$
--
--   Since $v^{\mathrm{HO}}$ bounds the expected revenue of every admissible policy, IRT loses a bounded amount of revenue against the optimal policy, whatever the horizon and the capacities, and in particular without any nondegeneracy assumption on the DLP.
--
--   **Formalization Note** The quantifier order is the content of the theorem: $M$ is chosen after $(n, m, \lambda, r, A)$ and before the optimal-solution selector, $T$ and $C$ (the paper's constant does not depend on which optimal solution the LP returns). The standing assumptions $\lambda > 0$, $r \ge 0$, $A \ge 0$, $C \ge 0$ are those of Sec. 2, p. 7, left implicit on the page. For $T \in \{1, 2\}$ (that is, $T \le e$) the printed $K$ is undefined or negative and the formalization takes $K = 0$ (IRT is SPA there). The re-solve right-hand side is the remaining capacity over the remaining time, $C(t^*_u)/\tau_u$ (Algorithm 3 prints the index $k$ for $u$).
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Theorem 1, p. 16; Algorithm 3, p. 15

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem irt_regret_uniformly_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℕ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C →
        hindsightValue A r lam (T : ℝ) C - irtValue A r lam sel (Kirt T) (T : ℝ) C ≤ M := by sorry

end ResolvingNRM.IRT
