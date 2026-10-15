-- Prove2me | Theorems.Thm_SuspensionContract_ControlBand_proposition_7
-- name    : SuspensionContract.ControlBand.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:22.93167+00:00
-- url     : https://prove2.me/theorems/23494374-42a3-4773-bbf5-ca7c4532caae
-- title:
--   Proposition 7, p. 28 — under Condition 3 the control-band value functions V_I, V_∅ of (46) satisfy the optimality condition (20)–(22)
-- statement:
--   Assume the standing assumptions and Condition 3 (either Condition 1 and $K<\bar K_1$, or Condition 2 and $K<\underline K$). Then there are parameters $(\mathsf c,\hat{\mathbf w},\bar\vartheta,\underline\vartheta)$ satisfying the conclusions of Proposition 6 such that the functions
--   $$V_I(w)=\begin{cases}V_{\mathsf c}(w),&w\in[0,\underline\vartheta),\\ \mathcal V_{\hat{\mathbf w}}(w),&w\ge\underline\vartheta,\end{cases}\qquad V_\emptyset(w)=\begin{cases}V_{\mathsf c}(w),&w\in[0,\bar\vartheta),\\ \mathcal V_{\hat{\mathbf w}}(w)-K,&w\ge\bar\vartheta,\end{cases}\qquad(46)$$
--   satisfy the optimality condition (20)–(22):
--   $$(\mathcal A_IV_I)(w)\ge0,\ (\mathcal A_\emptyset V_\emptyset)(w)\ge0\ (w>0),\qquad 0\le V_I(w)-V_\emptyset(w)\le K\ (w\ge0),\qquad V_I(0)\ge\underline v,\ V_\emptyset(0)\ge\underline v.$$
--
--   By the paper's verification Theorem 1 this pair certifies the optimality of the control-band contract (Theorem 5) in the low-switching-cost region.
--
--   **Formalization Note.** The statement is existential over the Proposition 6 tuple: the paper's proof uses properties of the specific tuple built in EC.3.9 beyond (42)–(45), and uniqueness of a tuple satisfying Proposition 6's conclusions was not checked; if it is unique the statement is exactly the paper's claim, otherwise it is implied by it. Condition (20) is posed for $w>0$: at $w=0$ the left derivative does not exist and $V_{\mathsf c}'(0^+)=+\infty$, so with Lean's junk derivative the inequality at $0$ would not express the paper's claim. The second claim of Proposition 7, (48) on the contract's utility $U(\hat\Gamma(w))$, belongs to the stochastic contract layer and is not stated.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 28, Proposition 7 (first claim); (46), p. 27; proof EC.3.10–EC.3.12, pp. ec40–ec51

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds

namespace SuspensionContract.ControlBand

theorem proposition_7 (P : Params) (hP : P.Standing) (h3 : P.Condition3) :
    ∃ c wB thHi thLo : ℝ, P.Prop6Params c wB thHi thLo ∧
      P.OptCond (P.VI46 c wB thLo) (P.V046 c wB thHi) := by sorry

end SuspensionContract.ControlBand
