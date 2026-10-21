-- Prove2me | Theorems.Thm_TechFinConstr_Selection_lemma_2
-- name    : TechFinConstr.Selection.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:03.833996+00:00
-- url     : https://prove2.me/theorems/f250a71d-274e-4aeb-85c9-ae5bf21b3d8b
-- title:
--   Lemma 2, p. 12 — the sign pattern of φ(p): negative at 0, ≤ 0 below ι̲(p), > 0 on [ι̲(p), ῑ(p)], = 0 above ῑ(p)
-- statement:
--   In Starmans' model, let $p\in\mathscr P$ and let $\bar\iota(p)$ be the highest state $i$ with $p_i>q_i$. Then there is a state $\underline\iota(p)$ with $1\le\underline\iota(p)\le\bar\iota(p)$ such that the likelihood ratio $\varphi_i(p)=(p_i-q_i)/q_i$ satisfies
--   $$\varphi_0(p)<0;\qquad \varphi_i(p)\le0\ \ (1\le i<\underline\iota(p));\qquad \varphi_i(p)>0\ \ (\underline\iota(p)\le i\le\bar\iota(p));\qquad \varphi_i(p)=0\ \ (\bar\iota(p)<i\le n).$$
--   In particular $\bar\iota(p)\in\{1,\dots,n\}$.
--
--   The lemma describes which region of the cash-flow distribution an entrepreneur improves: mass is moved from the low states to the states $\underline\iota(p),\dots,\bar\iota(p)$. The upper end $\bar\iota(p)$ governs which tranches are informative (Lemma 3) and is the parameter of the main comparison, Proposition 6.
--
--   **Formalization Note.** The paper introduces $\bar\iota(p)$ by this existence statement. Since the last clause forces $\varphi_i(p)=0$ above $\bar\iota(p)$ while $\varphi_{\bar\iota(p)}(p)>0$, the paper's $\bar\iota(p)$ is necessarily the highest state with $p_i>q_i$; the Lean statement fixes $\bar\iota(p)$ by that definition (`iotaBar`) and asserts the lemma for it, with $\underline\iota(p)$ existential.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 12, Lemma 2 (proof p. 40, Appendix A.5)

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

theorem lemma_2 {n : ℕ} (E : Economy n) (hE : E.Standing) (p : Fin (n + 1) → ℝ) (hp : InP E p) :
    ∃ lo : Fin (n + 1), 1 ≤ lo.val ∧ lo ≤ iotaBar E p ∧
      phi E p 0 < 0 ∧
      (∀ i : Fin (n + 1), 1 ≤ i.val → i < lo → phi E p i ≤ 0) ∧
      (∀ i : Fin (n + 1), lo ≤ i → i ≤ iotaBar E p → 0 < phi E p i) ∧
      (∀ i : Fin (n + 1), iotaBar E p < i → phi E p i = 0) := by sorry

end TechFinConstr.Selection
