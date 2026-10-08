-- Prove2me | Theorems.Thm_SecretaryWD_DiscUpper_class_payoff_lower_bound
-- name    : SecretaryWD.DiscUpper.class_payoff_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:18:48.688453+00:00
-- url     : https://prove2.me/theorems/c24b0fb8-1e99-4626-a55a-f69b88e5b762
-- title:
--   Proof of Thm 4.4 — the classical rule on $P_c$ earns at least $\mathsf{OPT}_c/2e$
-- statement:
--   In the discounted secretary problem with $n$ elements, values $v\ge0$ and discounts $d\ge0$, let $\mathcal A_c$ run the classical secretary rule on the arrivals at the times of the discount class $P_c$ only (observe the first $\lfloor |P_c|/e\rfloor$ of them, then select the first one ranking above all earlier arrivals of $P_c$), earning $d(i)v(\pi(i))$ at the selected time $i$. Then for every $c\ge1$,
--   $$\mathbb E[\mathcal A_c]\;\ge\;\frac{\mathsf{OPT}_c}{2e}.$$
--
--   The factor $e$ is the classical secretary guarantee; the additional factor $2$ is lost because $\mathcal A_c$ treats all discounts within $P_c$, which differ by at most a factor $2$, as equal.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, proof of Theorem 4.4 ("the classical secretary algorithm gets an expected value OPTc/2e")

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_Algorithm

namespace SecretaryWD.DiscUpper
theorem class_payoff_lower_bound (n : ℕ) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) (c : ℕ) (hc : 1 ≤ c) :
    optClass d v c / (2 * Real.exp 1) ≤ classValue d v c := by sorry
end SecretaryWD.DiscUpper
