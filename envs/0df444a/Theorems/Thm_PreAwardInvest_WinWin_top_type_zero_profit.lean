-- Prove2me | Theorems.Thm_PreAwardInvest_WinWin_top_type_zero_profit
-- name    : PreAwardInvest.WinWin.top_type_zero_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:58.406986+00:00
-- url     : https://prove2.me/theorems/0b4f4943-6da8-405e-9893-301aa06c740a
-- title:
--   Proof of Theorem 2, p. 43 (PDF 44) — the highest cost type earns zero: U^BIA_i(c̄_i) = 0 and U^BAI_i(c̄_i) = 0
-- statement:
--   Under the standing assumptions and ex ante symmetry, in every Bayesian Nash equilibrium $\beta$ of BIA (the buyer using Theorem 1's index policy) and in every Bayesian Nash equilibrium of BAI, the highest cost type of each supplier earns zero expected profit:
--
--   $$U^{\mathcal M}_i(\bar c_i)=u_i\big(\beta_i(\bar c_i);\bar c_i\big)=0\qquad\text{for all } i,\ \mathcal M\in\{\mathrm{BIA},\mathrm{BAI}\}.$$
--
--   The type $\bar c_i$ cannot bid above $\bar c_i$, loses money if he bids below and wins, and earns zero by bidding $\bar c_i$. This is the boundary term of the envelope formula (A.2).
--
--   **Formalization Note.** The ex ante symmetry condition is explicit, as in the proof of Theorem 2. The BAI boundary claim is stated for all suppliers within that setting.
-- source:
--   Chen, Beil & Duenyas, Procurement mechanisms with post-auction pre-award cost-reduction investigations, accepted manuscript (Operations Research 70(6), 2022; LBS Research Online eprint 2544), proof of Theorem 2, p. 43 (PDF 44)

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

namespace PreAwardInvest.WinWin

open MeasureTheory

theorem top_type_zero_profit {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing)
    (hsym : ExAnteSymmetric P) (τ : ℝ)
    (βI βA : Fin N → ℝ → ℝ) :
    (IsEqBIA P τ βI → ∀ i, profitBIA P τ βI i (βI i (cHiI P i)) (cHiI P i) = 0) ∧
      (IsEqBAI P βA → ∀ i, profitBAI P βA i (βA i (cHiI P i)) (cHiI P i) = 0) := by sorry

end PreAwardInvest.WinWin
