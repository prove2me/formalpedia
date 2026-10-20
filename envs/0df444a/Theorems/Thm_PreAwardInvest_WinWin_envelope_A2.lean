-- Prove2me | Theorems.Thm_PreAwardInvest_WinWin_envelope_A2
-- name    : PreAwardInvest.WinWin.envelope_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:54.344726+00:00
-- url     : https://prove2.me/theorems/f475ac0f-c7a8-471f-b8ec-fe2d25847d90
-- title:
--   Proof of Theorem 2, p. 43 (PDF 44), (A.2) — envelope formula U_i(c_i) = U_i(c̄_i) + ∫ φ_i(y) dy in BIA and BAI
-- statement:
--   Assume the standing assumptions. Let $\mathcal M$ be BIA (with Theorem 1's index policy) or BAI and let $\beta$ be a Bayesian Nash equilibrium of $\mathcal M$. Let $U^{\mathcal M}_i(c)=u_i(\beta_i(c);c)$ be supplier $i$'s equilibrium expected profit at cost $c$, and let
--
--   $$\phi^{\mathcal M}_i(y)=\mathbf E_{c_{-i}}\big[W_i(\beta_i(y),\beta_{-i}(c_{-i}))\big]$$
--
--   be his winning probability when he bids as cost type $y$ while the others bid truthfully to their types. Then for every $c\in C_i$,
--
--   $$U^{\mathcal M}_i(c)=U^{\mathcal M}_i(\bar c_i)+\int_{c}^{\bar c_i}\phi^{\mathcal M}_i(y)\,dy. \tag{A.2}$$
--
--   This is the envelope theorem for the suppliers' bidding games; it expresses equilibrium profit through winning probabilities alone.
--
--   **Formalization Note.** $W_i$ in BIA includes the expectation over the reductions $t$ (the paper's $\mathbf E_{c_{-i},t}$); in BAI it does not depend on $t$. Both mechanisms are stated in one theorem, each part under its own equilibrium hypothesis.
-- source:
--   Chen, Beil & Duenyas, Procurement mechanisms with post-auction pre-award cost-reduction investigations, accepted manuscript (Operations Research 70(6), 2022; LBS Research Online eprint 2544), proof of Theorem 2, p. 43 (PDF 44), (A.2)

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

namespace PreAwardInvest.WinWin

open MeasureTheory

theorem envelope_A2 {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing) (τ : ℝ)
    (βI βA : Fin N → ℝ → ℝ) :
    (IsEqBIA P τ βI → ∀ i, ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i),
      profitBIA P τ βI i (βI i c) c =
        profitBIA P τ βI i (βI i (cHiI P i)) (cHiI P i) +
          ∫ y in c..cHiI P i,
            ∫ cv, winProbBIA P τ (Function.update (bidProfile βI cv) i (βI i y)) i
              ∂(costVecLaw P)) ∧
    (IsEqBAI P βA → ∀ i, ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i),
      profitBAI P βA i (βA i c) c =
        profitBAI P βA i (βA i (cHiI P i)) (cHiI P i) +
          ∫ y in c..cHiI P i,
            ∫ cv, winProbBAI P (Function.update (bidProfile βA cv) i (βA i y)) i
              ∂(costVecLaw P)) := by sorry

end PreAwardInvest.WinWin
