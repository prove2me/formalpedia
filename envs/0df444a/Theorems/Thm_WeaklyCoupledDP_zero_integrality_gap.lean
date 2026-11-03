-- Prove2me | Theorems.Thm_WeaklyCoupledDP_zero_integrality_gap
-- name    : WeaklyCoupledDP.zero_integrality_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:43.88393+00:00
-- url     : https://prove2.me/theorems/abce6935-7393-4dea-b25c-05fcaf8a3934
-- title:
--   Proof of Theorem 4.8 — under Assumption 4.7 every separation problem has zero integrality gap
-- statement:
--   Suppose Assumption 4.7 holds. Then for every candidate solution $V = (V_{t,i}(s_{t,i},e_t))$, every period $1 \le t \le T$ and every exogenous state $e_t$, the $(t,e_t)$-separation problem (6) and its LP relaxation (9) have the same optimal value:
--   $$
--   \Delta^V_t(e_t,\ell_t,b_t) = 0 .
--   $$
--   Because the linking vectors do not depend on the subproblem states, the separation problem collapses to an integer program in the variables $x_{t,i}(e_t,a_{t,i})$, $a_{t,i} \in \bar A_{t,i}(e_t)$, whose constraint matrix is the totally unimodular matrix of (12) with an integral right-hand side. This is the step through which Assumption 4.7 enters Theorem 4.8.
--
--   Differences from the source:
--   - encoding: Δ^V_t as the difference of two minima → the difference of two infima (sInf); reason: for 1 ≤ t ≤ T both feasible sets are nonempty and compact, so both infima are attained minima and the values agree.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §4.3, p.15 (PDF p.16); proof of Theorem 4.8, pp.31–32 (PDF pp.32–33)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_integralityGap
import Definitions.Def_WeaklyCoupledDP_Model_Assumption47

namespace WeaklyCoupledDP

/-- **Zero integrality gap under Assumption 4.7** (Brown & Zhang, SSRN 3849573 (Feb. 6, 2022), §4.3,
p.15, and the proof of Theorem 4.8, pp.31–32). Under Assumption 4.7, for every candidate `V`, every
period `1 ≤ t ≤ T` and every exogenous state `eₜ`, the integrality gap of the separation problem (6)
is zero: `Δ^V_t(eₜ, ℓₜ, bₜ) = 0`. -/
theorem zero_integrality_gap {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*}
    {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ} [∀ t i, Fintype (S t i)] [Fintype E]
    (M : Model N S E Act L) (h : M.Assumption47) (V : M.ValueArray) (t : ℕ) (h1 : 1 ≤ t)
    (hT : t ≤ M.T) (e : E) :
    M.integralityGap V t e = 0 := by sorry

end WeaklyCoupledDP
