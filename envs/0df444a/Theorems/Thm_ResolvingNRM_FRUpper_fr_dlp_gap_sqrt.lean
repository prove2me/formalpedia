-- Prove2me | Theorems.Thm_ResolvingNRM_FRUpper_fr_dlp_gap_sqrt
-- name    : ResolvingNRM.FRUpper.fr_dlp_gap_sqrt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:44:14.042153+00:00
-- url     : https://prove2.me/theorems/7685986f-5ae9-42f1-b07c-7c6802936514
-- title:
--   Proposition 3 — v^DLP − v^FR = O(√T), uniformly in the capacities
-- statement:
--   Consider the network revenue management model with $n$ customer classes and $m$ resources: Poisson arrival rates $\lambda_j > 0$, revenues $r_j \ge 0$, and a nonnegative bill-of-materials matrix $A = (a_{lj})$. For an integer horizon $T \ge 1$ and initial capacity $C \ge 0$, let $v^{\mathrm{DLP}}(T, C) = T\, v(C/T)$ be the value of the deterministic LP (2), and $v^{\mathrm{FR}}(T, C)$ the expected revenue of the Frequent Re-solving policy (Algorithm 2), which re-solves the LP at every integer time and uses any optimal solution. There is a constant $M$, depending only on $\lambda$, $r$ and $A$, such that for every optimal-solution selector, every $T \ge 1$ and every $C \ge 0$,
--   $$v^{\mathrm{DLP}}(T, C) - v^{\mathrm{FR}}(T, C) \ \le\ M \sqrt{T}.$$
--
--   Since $v^{\mathrm{DLP}}$ upper-bounds the expected revenue of every admissible policy, the revenue loss of FR is $O(\sqrt{T})$ without any nondegeneracy assumption on the DLP. The paper combines this with Proposition 2, an $\Omega(\sqrt{T})$ lower bound on a degenerate instance, to conclude $v^* - v^{\mathrm{FR}} = \Theta(\sqrt{T})$ there.
--
--   **Formalization Note.** "$= O(\sqrt{T})$" is formalized with the constant chosen after $(n, m, \lambda, r, A)$ and before the selector, $T$ and $C$; this is the paper's statement that the constant "does not depend on the starting capacity $C_l$". The paper's threshold $T_1$ in the definition of $O(\cdot)$ (p. 7) is dropped: the bound is stated for all $T \ge 1$, which is equivalent because $0 \le v^{\mathrm{FR}}$ and $v^{\mathrm{DLP}} \le T \sum_j r_j \lambda_j$, so the gap is bounded on any finite range of $T$ uniformly in $C$. $\lambda_j > 0$, $r \ge 0$, $a_{lj} \ge 0$, $C \ge 0$ are the model's standing assumptions (p. 7).
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Proposition 3, p. 19 (proof App. C.2, pp. 34–36)

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.FRUpper

/-- Proposition 3, p. 19: `v^DLP − v^FR = O(√T)`, with a constant that depends on `λ`, `r` and `A`
but not on the starting capacity `C` (nor on the optimal LP solutions chosen). -/
theorem fr_dlp_gap_sqrt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), ResolvingNRM.IRT.IsDLPSelector A r lam sel →
      ∀ T : ℕ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C →
        ResolvingNRM.IRT.dlpValue A r lam T C - frValue A r lam sel T C ≤ M * Real.sqrt T := by sorry

end ResolvingNRM.FRUpper
