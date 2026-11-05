-- Prove2me | Theorems.Thm_RailwayRM_theorem_2
-- name    : RailwayRM.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:18.342359+00:00
-- url     : https://prove2.me/theorems/47c9e5de-0346-4a82-9278-28f351f24da3
-- title:
--   Theorem 2: the static-price flexible-capacity policy has an $O(\sqrt\kappa)$ gap and is asymptotically optimal (corrected: needs $b^*_{u,m}<\bar b_m$, and $J_D\ne0$ for the ratio)
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$ with $b^*_{u,m}<\bar b_m$ for all $m$. In the $\kappa$-scaled problem $P_{S,\kappa}$, let $\pi_1$ be the static-price flexible-capacity policy built from $(\vec x^*,\vec y^*,\kappa\vec b^*_u)$, with any selection of minimizers in its capacity step, and let $J^{\pi_1}_{S,\kappa}$ be its expected profit.
--
--   There is a constant $C$, independent of $\kappa$ and of the selection, such that for every integer $\kappa\ge1$:
--
--   1. $\pi_1$ is feasible for $P_{S,\kappa}$;
--   2. the profits of the feasible policies of $P_{S,\kappa}$ are bounded above, every feasible policy earns at most $J^{\pi_1}_{S,\kappa}+C\sqrt\kappa$, and
--   $$\big|J_{S,\kappa}-J^{\pi_1}_{S,\kappa}\big|\le C\sqrt\kappa.$$
--
--   Consequently, if $J_D\ne0$, then for any choice of selections
--   $$\frac{J^{\pi_1}_{S,\kappa}}{J_{S,\kappa}}\longrightarrow1\quad\text{as }\kappa\to\infty.$$
--
--   So a single pricing rule with a stopping condition and a capacity decision at the end of the horizon captures the optimal profit up to a term of order $\sqrt\kappa$, while that profit grows like $\kappa$.
--
--   **Formalization Note.** The bound against each feasible policy makes the statement independent of the junk values of `sSup`. $J_D$ is the objective value of $P_D$ at the given optimal solution.
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
--   - reading: E in Q^{π1} (p. 16) → expectation conditional on the observed path, stated for every selection of minimizers; reason: B^{π1} is random and the coaches are chosen at the end of the horizon, so (8) needs the conditional form
--   - reading: "the capacities are all scaled by κ" (p. 17) → b̄_m and b̲_m both scale by κ; reason: App. p. 6 says the solution of P_{D,κ} is (x⃗*, y⃗*, κb⃗*_u), which fails if b̲_m does not scale and binds
--   - correction: no condition on b*_{u,m} → hypothesis b*_{u,m} < b̄_m for every m; reason: at b*_{u,m} = b̄_m the threshold of step 2 is 0 and π1 stops after period 1. Counterexample: L = N = M = 1, δ = 1, T = 4, k = 1, b̄ = 1, b̲ = 0, c_o = 0.1, c_s = 1, r(x, y) = x(0.1 − x) + y(3 − y) on [0, 0.3] × [0, 0.6]: the optimum has b* = b̄ and the gap is linear in κ
--   - correction: the ratio tends to 1 for every instance → hypothesis J_D ≠ 0 on the ratio clause; reason: with J_D = 0 the ratio can be 0/0. Counterexample: L = N = M = 1, δ = 1, T = k = b̄ = 1, b̲ = 0, c_o = c_s = 10, r(x, y) = x(1 − x) + y(1 − y) on [0, 0.4]²: selling nothing is optimal and J_{S,κ} = J^{π1}_{S,κ} = 0
--   - encoding: O(√κ) in κ ∈ ℕ → ∃ C, ∀ κ ≥ 1 (κ : ℕ+), |·| ≤ C √κ; reason: the bound holds for every κ ≥ 1, not only eventually; C comes before κ
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), Theorem 2, p. 17; policy π1, p. 16; proof, App. pp. 2–5

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

open Filter Topology

namespace RailwayRM

/-- **Theorem 2, corrected** (Manchiraju et al., SSRN 4112672 (2023-08-22), Theorem 2, p. 17): the
difference between the optimal profit of `P_{S,κ}` and the profit of the static-price flexible-capacity
policy `π₁` in `P_{S,κ}` is `O(√κ)`, and, if `J_D ≠ 0`, the ratio `J^{π₁}_{S,κ} / J_{S,κ}` tends to `1`.

For every instance and every optimal solution `(x⃗*, y⃗*, b⃗*_u)` of `P_D` with `b*_{u,m} < b̄_m`,
there is `C`, independent of `κ` and of the selection, such that for every `κ ≥ 1` and every selection
of minimizers in `P_{S,κ}`: `π₁` is feasible, the profits of the feasible policies are bounded above,
every feasible policy earns at most `J^{π₁}_{S,κ} + C √κ`, and `|J_{S,κ} - J^{π₁}_{S,κ}| ≤ C √κ`.

**Formalization Note.** Both hypotheses beyond the page are corrections. At `b*_{u,m} = b̄_m` the
threshold of step 2 is `0` and the gap is linear in `κ`. At `J_D = 0` the ratio can be `0 / 0`.
`π₁` in `P_{S,κ}` is `pi1` of the scaled instance at the solution `(x⃗*, y⃗*, κ b⃗*_u)` of `P_{D,κ}`.
The bound against each feasible policy makes the statement independent of the junk values of
`sSup`. -/
theorem theorem_2 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) (hb : ∀ m, b m < (I.bMax m : ℝ)) :
    (∃ C : ℝ, ∀ (κ : ℕ+) (sel : (I.scale κ).ObsPath → Fin M → ℝ),
      (I.scale κ).IsCapacitySelection v (scaleCoaches κ b) sel →
        (I.scale κ).IsFeasible ((I.scale κ).pi1 v (scaleCoaches κ b) sel) ∧
        BddAbove (I.scale κ).profits ∧
        (∀ π : (I.scale κ).Policy, (I.scale κ).IsFeasible π →
          (I.scale κ).profit π ≤
            (I.scale κ).profit ((I.scale κ).pi1 v (scaleCoaches κ b) sel) +
              C * Real.sqrt ((κ : ℕ) : ℝ)) ∧
        |(I.scale κ).JS - (I.scale κ).profit ((I.scale κ).pi1 v (scaleCoaches κ b) sel)| ≤
          C * Real.sqrt ((κ : ℕ) : ℝ)) ∧
    (I.detProfit v b ≠ 0 →
      ∀ sel : (κ : ℕ+) → (I.scale κ).ObsPath → Fin M → ℝ,
        (∀ κ, (I.scale κ).IsCapacitySelection v (scaleCoaches κ b) (sel κ)) →
          Tendsto (fun κ : ℕ+ =>
            (I.scale κ).profit ((I.scale κ).pi1 v (scaleCoaches κ b) (sel κ)) / (I.scale κ).JS)
            atTop (𝓝 1)) := by sorry

end RailwayRM
