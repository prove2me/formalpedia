-- Prove2me | Theorems.Thm_PreAwardInvest_WinWin_proposition_1
-- name    : PreAwardInvest.WinWin.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:00.406562+00:00
-- url     : https://prove2.me/theorems/bb4e1360-6faa-4073-8b6a-85c974107d79
-- title:
--   Proposition 1, p. 13 (PDF 14) — existence of a shifted first-price-auction equilibrium in BAI
-- statement:
--   Consider the first-price sealed-bid procurement auction in which supplier $i$'s cost is $\check c_i=c_i-r_i$, with $r_i=\max\{0,\Delta^t_i-d\}$, bids lie in $[-r_i,\bar c_i-r_i]$, the lowest bid wins and ties are broken at random. There exists a Bayesian Nash equilibrium $(\check\beta_i)_{i\in\mathcal N}$ of that auction such that the shifted strategies
--
--   $$\tilde\beta_i(c_i):=\check\beta_i(c_i-r_i)+r_i,\qquad c_i\in C_i,$$
--
--   form a Bayesian Nash equilibrium of BAI.
--
--   In BAI the buyer awards the contract to the lowest $\lambda_i=b_i-r_i$, so BAI is strategically a first-price auction with costs $c_i-r_i$. The paper invokes Athey (2001) for the existence of an equilibrium of that auction; with it, the proposition gives an equilibrium of BAI.
--
--   **Formalization Note.** The existence of the first-price equilibrium is included in the conclusion, as the paper states; its proof cites Athey (2001). The section's Assumptions 1 and 2 are explicit binders. The first-price bid space is $[-r_i,\bar c_i-r_i]=B_i-r_i$, the exact image of $B_i=[0,\bar c_i]$ under $b\mapsto b-r_i$; the proof on p. 39 writes $[\underline c_i-r_i,\bar c_i-r_i]$ and then notes that bids below cost are suboptimal.
-- source:
--   Chen, Beil & Duenyas, Procurement mechanisms with post-auction pre-award cost-reduction investigations, accepted manuscript (Operations Research 70(6), 2022; LBS Research Online eprint 2544), p. 13 (PDF 14), Proposition 1; proof p. 39 (PDF 40)

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

namespace PreAwardInvest.WinWin

open MeasureTheory

theorem proposition_1 {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P) :
    ∃ βc : Fin N → ℝ → ℝ,
      IsEqFPA P βc ∧
        IsEqBAI P (fun i c => βc i (c - rBAI P i) + rBAI P i) := by sorry

end PreAwardInvest.WinWin
