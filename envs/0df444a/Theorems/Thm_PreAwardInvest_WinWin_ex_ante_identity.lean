-- Prove2me | Theorems.Thm_PreAwardInvest_WinWin_ex_ante_identity
-- name    : PreAwardInvest.WinWin.ex_ante_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:56.559517+00:00
-- url     : https://prove2.me/theorems/2a2866cf-fcdc-4662-a7b9-0ba611a2caae
-- title:
--   Proof of Theorem 2, p. 43 (PDF 44) — ex ante profit E[U_i(c_i)] = U_i(c̄_i) + E[A_i(c,t) F_i(c_i)/f_i(c_i)] in BIA and BAI
-- statement:
--   Assume the standing assumptions. Let $\mathcal M$ be BIA (with Theorem 1's index policy) or BAI and let $\beta$ be a Bayesian Nash equilibrium of $\mathcal M$. Write $A^{\mathcal M}_i(c)=W_i(\beta_1(c_1),\dots,\beta_N(c_N))$ for supplier $i$'s winning probability at the cost vector $c$ (in BIA this averages over $t$). Then supplier $i$'s ex ante expected profit satisfies
--
--   $$\mathbf E_{c_i}\big[U^{\mathcal M}_i(c_i)\big]=U^{\mathcal M}_i(\bar c_i)+\mathbf E_{c}\Big[A^{\mathcal M}_i(c)\,\frac{F_i(c_i)}{f_i(c_i)}\Big].$$
--
--   The ratio $F_i/f_i$ is the virtual-cost term of a procurement auction; the identity is the standard derivation (Myerson 1981) from the envelope formula (A.2).
--
--   **Formalization Note.** $F_i(c_i)/f_i(c_i)$ is evaluated at the random cost $c_i$, which lies in the open support, where $f_i>0$, almost surely. The paper's $\mathbf E_{c_i}[U^{\mathcal M}_i(\bar c_i)]$ is the constant $U^{\mathcal M}_i(\bar c_i)$.
-- source:
--   Chen, Beil & Duenyas, Procurement mechanisms with post-auction pre-award cost-reduction investigations, accepted manuscript (Operations Research 70(6), 2022; LBS Research Online eprint 2544), proof of Theorem 2, p. 43 (PDF 44)

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

namespace PreAwardInvest.WinWin

open MeasureTheory

theorem ex_ante_identity {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing) (τ : ℝ)
    (βI βA : Fin N → ℝ → ℝ) :
    (IsEqBIA P τ βI → ∀ i,
      exAnteBIA P τ βI i =
        profitBIA P τ βI i (βI i (cHiI P i)) (cHiI P i) +
          ∫ cv, winProbBIA P τ (bidProfile βI cv) i * (Fi P i (cv i) / fi P i (cv i))
            ∂(costVecLaw P)) ∧
    (IsEqBAI P βA → ∀ i,
      exAnteBAI P βA i =
        profitBAI P βA i (βA i (cHiI P i)) (cHiI P i) +
          ∫ cv, winProbBAI P (bidProfile βA cv) i * (Fi P i (cv i) / fi P i (cv i))
            ∂(costVecLaw P)) := by sorry

end PreAwardInvest.WinWin
