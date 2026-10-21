-- Prove2me | Theorems.Thm_ReportDepSP_Honesty_payoff_le_of_condition3
-- name    : ReportDepSP.Honesty.payoff_le_of_condition3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:05.336005+00:00
-- url     : https://prove2.me/theorems/c9a6c7a5-40b4-4506-a928-bb00a8202522
-- title:
--   Proof of Proposition 2, p. 13 — if (3) holds against R̃, the truth is weakly better than R̃ for every decreasing ρ
-- statement:
--   Let $P\ge 0$ be a nonnegative weight function on attainability states, $\widetilde R$ a ROL, and $v$ a payoff vector with $v_1\ge v_2\ge\dots\ge v_n$. Suppose condition (3) holds for $\widetilde R$:
--   $$\sum_{r=1}^{\bar r}\bigl(f_r - \widetilde f_r\bigr)\ \ge\ 0 \qquad\forall\,\bar r\in⟦1,n⟧ .$$
--   Then for every (weakly) decreasing $\rho:⟦1,n⟧\to\mathbb R$,
--   $$U(v\mid \widetilde R)\ \le\ U(v\mid R).$$
--
--   This is the "if" direction of Proposition 2.
--
--   **Formalization Note** The paper concludes "$> 0$" for $\Delta_\rho$; the strict inequality fails when (3) holds with equality (e.g. two options with independent, fair-coin attainability, where the true list and the swapped list have the same match probabilities), so the statement is weak. It is stated for every antitone (weakly decreasing) $\rho$, which contains the strictly decreasing $\rho$ of the model; the paper's argument only uses that the gaps $\rho(r)-\rho(r+1)$ are nonnegative. The decreasing order of $v$ is the paper's standing relabeling (p. 5). Ranks and options are 0-indexed `Fin n`; the true ROL is `1`.
-- source:
--   Meisner, Report-dependent utility and strategy-proofness, CRC TRR 190 Discussion Paper No. 289 (2021; Management Science doi:10.1287/mnsc.2022.4504), proof of Proposition 2 (Appendix), third paragraph, p. 13

import Mathlib
import Definitions.Def_ReportDepSP_Honesty_Setting

namespace ReportDepSP.Honesty

open Finset

/-- Proof of Proposition 2 (p. 13), "if": when condition (3) holds for `Rt`, the true ROL is
weakly better than `Rt` for every decreasing `v` and every (weakly) decreasing `ρ`. -/
theorem payoff_le_of_condition3 {n : ℕ} (P : (Fin n → Bool) → ℝ) (Rt : Equiv.Perm (Fin n))
    (hP0 : ∀ a, 0 ≤ P a) (v : Fin n → ℝ) (hv : Antitone v) (h3 : Condition3 P Rt) :
    ∀ ρ : Fin n → ℝ, Antitone ρ → payoff v ρ P Rt ≤ payoff v ρ P 1 := by sorry

end ReportDepSP.Honesty
