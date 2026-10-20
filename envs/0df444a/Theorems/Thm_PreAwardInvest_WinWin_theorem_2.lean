-- Prove2me | Theorems.Thm_PreAwardInvest_WinWin_theorem_2
-- name    : PreAwardInvest.WinWin.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:03.513057+00:00
-- url     : https://prove2.me/theorems/9b511197-69d4-41a1-86b9-4291512f4891
-- title:
--   Theorem 2, p. 19 (PDF 20) — ex ante symmetric suppliers earn at least as much ex ante expected profit in BIA as in BAI (weak form)
-- statement:
--   Assume the standing assumptions of §3.1, Assumption 1 ($F_i/f_i$ nondecreasing) and Assumption 2 ($d<\max_i\Delta^t_i$), and suppose that the suppliers are **ex ante symmetric**: $\Delta^c_i=\Delta^c$ and $\Delta^t_i=\Delta^t$ for all $i\in\mathcal N$. Let $\tau$ solve $d=\int_\tau^\infty(\epsilon^t-\tau)\,dG(\epsilon^t)$, so that the buyer in BIA uses the index policy of Theorem 1. Let $\beta^{\mathrm{BIA}}$ be a symmetric Bayesian Nash equilibrium of BIA, and $\beta^{\mathrm{BAI}}$ a symmetric Bayesian Nash equilibrium of BAI whose common strategy is nondecreasing in cost. Then every supplier $i$ earns at least as much ex ante expected profit in BIA as in BAI:
--
--   $$\mathbf E_{c_i}\Big[u^{\mathrm{BAI}}_i\big(\beta^{\mathrm{BAI}}_i(c_i);c_i\big)\Big]\le\mathbf E_{c_i}\Big[u^{\mathrm{BIA}}_i\big(\beta^{\mathrm{BIA}}_i(c_i);c_i\big)\Big].$$
--
--   This is the paper's win-win result: investigating before the award lowers the buyer's cost (conditionally on bids) and, with symmetric suppliers, does not hurt any supplier ex ante, because the investigations soften price competition at the bidding stage.
--
--   **Formalization Note.** The printed theorem says "higher"; the strict inequality is false (with one supplier both mechanisms give the lone supplier exactly $\bar c_1-c_1$, and the proof on p. 43 concludes with "$\le$"), so the weak inequality is stated. The proof's "by symmetry" needs symmetric equilibria and a mechanism invariant under relabelling; both equilibria are assumed symmetric, and ties are broken by a uniformly random priority. The BAI equilibrium is nondecreasing, the class of Lemma 1 and §4.2, which the proof uses for "$A^{\mathrm{BAI}}_i(c)=1$ iff $c_i<\min_{j\ne i}c_j$". $\tau$ is any root of its equation. Strategies are measurable. Ex ante profit is the expectation of (5), not the Myerson expression.
-- source:
--   Chen, Beil & Duenyas, Procurement mechanisms with post-auction pre-award cost-reduction investigations, accepted manuscript (Operations Research 70(6), 2022; LBS Research Online eprint 2544), p. 19 (PDF 20), Theorem 2; proof p. 43 (PDF 44)

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

namespace PreAwardInvest.WinWin

open MeasureTheory

theorem theorem_2 {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing) (hA1 : Assumption1 P)
    (hA2 : Assumption2 P) (hsym : ExAnteSymmetric P) (τ : ℝ) (hτ : IsTauRoot P τ)
    (βI βA : Fin N → ℝ → ℝ)
    (hI : IsEqBIA P τ βI) (hIsym : ∀ i j, βI i = βI j)
    (hA : IsEqBAI P βA) (hAsym : ∀ i j, βA i = βA j)
    (hAmono : ∀ i, MonotoneOn (βA i) (Set.Icc (cLoI P i) (cHiI P i))) :
    ∀ i, exAnteBAI P βA i ≤ exAnteBIA P τ βI i := by sorry

end PreAwardInvest.WinWin
