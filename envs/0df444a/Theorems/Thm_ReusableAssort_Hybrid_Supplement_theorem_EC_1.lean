-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_Supplement_theorem_EC_1
-- name    : ReusableAssort.Hybrid.Supplement.theorem_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:20:34.714741+00:00
-- url     : https://prove2.me/theorems/4720e247-4b95-448a-949f-3459a8d2bba3
-- title:
--   Theorem EC.1, p. ec4 — Expected-LP can be a (4/T)-fraction of the optimum offline
-- statement:
--   For every horizon $T \ge 1$ there is an instance of the model (finitely many products and types, satisfying the model assumptions) such that every feasible LP value is at most $2$, the optimum offline value is at least $T/2$ for every valid choice law, and Expected-LP$[\{F_t\}_{t=1}^T]$ has a feasible solution of positive value, and for every valid joint law of the consumers' choices and every feasible LP solution $y$,
--   $$\mathrm{LP}(y) \le \frac{4}{T}\,\mathrm{OPT}_{\mathrm{off}}.$$
--
--   So the Bayesian expected LP is at most an $O(1/T)$-approximation to the optimum offline benchmark, and no online algorithm has a $T$-independent competitive ratio against the optimum offline (Corollary EC.1, with Proposition 1). This is a companion theorem; it is not used in the proof of the goal.
--
--   Differences from the source:
--   - reading: Expected-LP is at most an O(1/T)-approximation to the optimum offline → for every T ≥ 1 there is an instance satisfying the model assumptions, with a positive feasible LP value, every feasible LP value at most 2, offline value at least T/2 for every valid law, and lpObj I y ≤ (4/T) · optOffline for every feasible y; reason: the proof separately gives LP ≤ 2 by θ_T = 2 and offline ≥ T/2; the explicit bound and positivity avoid an unspecified constant or zero witness
--   - generalization: exact realizations of consumer choices for each possible assortment (no joint law specified) → the bound holds for every joint law of choice functions per time and type, independent across times, whose marginal at each S ∈ 𝒮 is ϕ^z(S, ·); reason: the source leaves the joint law open; any law it intends has these marginals, so the Lean statement specializes to it
--   - reading: rental duration 'infinite' → duration T (a unit rented at t ≥ 1 is not back before T + 1); reason: the base model's durations lie in {1, …, T}; within the horizon a duration T unit never returns
--   - encoding: optimum offline: the offline algorithm with full information picks assortments of available products → optOffline = expectation over (types, durations d_{t,i} for every time and product, choice functions) of the maximum revenue over sequences A_t ∈ 𝒮 in which every offered product has a unit on hand on that realization; the realization law is independent across times and factors, conditional on type, into independent product durations and a choice function; reason: direct encoding of §EC.2 item 1 with the base model's return convention (a unit rented at t with duration d is out at t, …, t + d − 1); the source does not specify the joint counterfactual duration law across products, so this definition chooses the conditional product coupling. The proof witness has one product and deterministic choices, making that choice immaterial to the theorem
--   - reading: the model of §2.1 (types ⟨ϕ^z, r^z, G^z⟩, Assumptions 1–2, c_i ∈ ℤ₊, durations g^z_i on [T]) → the published base Instance.Assumptions: one finite type space, durations on {1, …, T}, ϕ^z(S, ·) a sub-probability on S, weak substitutability on 𝒮, 𝒮 nonempty and downward closed, r ≥ 0, c_i ≥ 1; reason: these are the base mission's disclosed readings of the model, reused unchanged by reference
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec4 (PDF 30), Theorem EC.1 and its proof

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_Offline

namespace ReusableAssort.Hybrid.Supplement

theorem theorem_EC_1 (T : ℕ) (hT : 1 ≤ T) :
    ∃ (n m : ℕ) (I : Instance n T (Fin m)), I.Assumptions ∧
      (∃ y, LPFeasible I y ∧ 0 < lpObj I y) ∧
      (∀ y, LPFeasible I y → lpObj I y ≤ 2) ∧
      ∀ law, ValidChoiceLaw I law → (T : ℝ) / 2 ≤ optOffline I law ∧
        ∀ y, LPFeasible I y → lpObj I y ≤ (4 / (T : ℝ)) * optOffline I law := by sorry

end ReusableAssort.Hybrid.Supplement
