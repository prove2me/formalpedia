-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_spa_dlp_gap_sqrt
-- name    : ResolvingNRM.IRT.spa_dlp_gap_sqrt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:20:58.409323+00:00
-- url     : https://prove2.me/theorems/4bf9ec79-5c84-496f-b732-836da6909503
-- title:
--   Proposition 5, p. 27 — static probabilistic allocation loses $O(\sqrt T)$ against the DLP, uniformly in $C$
-- statement:
--   Fix the data of the network revenue-management model: Poisson rates $\lambda_j > 0$, revenues $r_j \ge 0$ and a nonnegative bill-of-materials matrix $A$. The **static probabilistic allocation** (SPA) heuristic (Algorithm 1) solves the DLP once at $b = C/T$, obtaining an optimal $x^*$, and accepts each class-$j$ arrival with probability $x^*_j/\lambda_j$ whenever capacity allows. Let $v^{\mathrm{SPA}}(T, C)$ be its expected revenue.
--
--   There is a constant $M$, depending only on $(\lambda, r, A)$, such that for every choice of optimal DLP solutions, every horizon $T > 0$ and every capacity $C \ge 0$,
--   $$v^{\mathrm{DLP}}(T, C) - v^{\mathrm{SPA}}(T, C) \le M\sqrt{T}.$$
--
--   The bound holds uniformly in the capacity, with no scaling assumption linking $C$ and $T$; this is what lets the proof of Theorem 1 apply it to the last epoch of IRT, whose starting capacity is random.
--
--   **Formalization Note** SPA is the member $\mathrm{IRT}^0$ of the IRT family (one epoch, plain probabilities from $\mathrm{sel}(C/T)$). $M$ is chosen before the selector, $T$ and $C$: the paper's constant $\sum_l r^l_{\max}\sqrt{\sum_j a_{lj}^2\lambda_j}$ does not depend on which optimal solution the LP returns. The horizon $T$ is a positive real, because the proof of Theorem 1 applies the result on the sub-horizon $\tau_K = T^{(5/6)^K}$ (eq. (11)). The standing assumptions $\lambda > 0$, $r \ge 0$, $A \ge 0$, $C \ge 0$ are those of Sec. 2, p. 7, left implicit on the page.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Proposition 5, p. 27 (Appendix A.2); Algorithm 1, p. 10

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem spa_dlp_gap_sqrt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℝ, 0 < T → ∀ C : Fin m → ℝ, 0 ≤ C →
        dlpValue A r lam T C - irtValue A r lam sel 0 T C ≤ M * Real.sqrt T := by sorry

end ResolvingNRM.IRT
