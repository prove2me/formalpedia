-- Prove2me | Theorems.Thm_RailwayRM_theorem_1
-- name    : RailwayRM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:22.818989+00:00
-- url     : https://prove2.me/theorems/7dc2f498-e951-4cec-bdcf-b428211b1801
-- title:
--   Theorem 1: $J_S\le J_D$
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of the deterministic problem $P_D$, with value $J_D$. Then every feasible policy $\pi$ of the stochastic problem $P_S$ has expected profit at most $J_D$, and therefore
--   $$J_S\le J_D.$$
--
--   The deterministic problem is the upper bound against which every policy of the mission is measured.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - encoding: Π is the class of non-anticipatory policies (p. 13) → deterministic functions of the observed history, rates before t only and coaches of the whole observed path; reason: a randomized policy is a mixture of these and cannot beat the supremum
--   - encoding: (2) is printed without "(a.s.)" (p. 14) → (1) and (2) both hold on paths of positive probability; reason: a policy can be changed on null paths without changing its law or profit
--   - encoding: "max" over Π (p. 13) → J_S is the supremum sSup of the profits of feasible policies; reason: attainment is not claimed anywhere; the bound against each feasible policy is stated as well
--   - reading: footnote 2, p. 12: ⌈x⌉ = ⌊x⌋ + 1 → the usual ceiling Nat.ceil; reason: the footnote differs at integers and contradicts the equivalence of (1) and (3), p. 14, and "the minimum number of reserved coaches sufficient", p. 16
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
--   - encoding: J_D = max of P_D (p. 15) → the objective of P_D at a given optimal solution (v, b), hypothesis IsOptimalD; reason: the paper writes max, presupposing attainment (Λ_n need not be closed); without an optimum J_D is undefined
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), Theorem 1, p. 15

import Mathlib
import Definitions.Def_RailwayRM_Model

namespace RailwayRM

/-- **Theorem 1** (Manchiraju et al., SSRN 4112672 (2023-08-22), Theorem 1, p. 15): the optimal
profit of `P_S` is at most that of `P_D`, `J_S ≤ J_D`.

**Formalization Note.** `J_D` is the objective value at an optimal solution `(v, b)` of `P_D`, which
the paper assumes to exist. The bound is also stated for each feasible policy, so it does not rest on
the value of `sSup`. -/
theorem theorem_1 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) :
    (∀ π : I.Policy, I.IsFeasible π → I.profit π ≤ I.detProfit v b) ∧ I.JS ≤ I.detProfit v b := by sorry

end RailwayRM
