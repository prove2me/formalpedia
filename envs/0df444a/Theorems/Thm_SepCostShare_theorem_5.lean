-- Prove2me | Theorems.Thm_SepCostShare_theorem_5
-- name    : SepCostShare.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:59.663868+00:00
-- url     : https://prove2.me/theorems/eeeea24a-380e-4418-916d-b62549a88ac0
-- title:
--   Theorem 5 — Algorithm 1 returns a no costlier enforceable profile within $n\cdot m\cdot\mathrm{rk}(\mathcal B)$ iterations (corrected: (2) on used resources)
-- statement:
--   Let $\mathcal M$ be a matroid game (a matroid congestion model) with subadditive costs, $n=|N|$, $m=|E|$, $\mathrm{rk}(\mathcal B)=\max_{i\in N}\mathrm{rk}_i$, and let $B$ be a strategy profile. Run Algorithm 1 on $B$, with any choice of resource, player and minimizer at every step. Then:
--
--   1. every run performs at most $n\cdot m\cdot\mathrm{rk}(\mathcal B)$ iterations of the while-loop of Line 2, and at most $n\cdot m\cdot\mathrm{rk}(\mathcal B)$ exchanges in total (iterations of Lines 3–5 plus iterations of the loop of Line 7);
--   2. whenever a run stops (control at Line 2 and no resource satisfies (1) or (2)), its profile $B'$ is enforceable and
--   $$C(B')\le C(B);$$
--   3. Algorithm 1 is well defined: a run that has not stopped can always perform a further step;
--   4. in particular there is an enforceable profile $B'$ with $C(B')\le C(B)$ that a run of Algorithm 1 computes within $n\cdot m\cdot\mathrm{rk}(\mathcal B)$ exchanges.
--
--   This is a black-box reduction: starting from any profile, e.g. the output of an approximation algorithm, it returns a profile that a separable cost sharing protocol can enforce as a pure Nash equilibrium, at no higher cost.
--
--   Differences from the source:
--   - generalization: there is an enforceable B′ with C(B′) ≤ C(B) that can be computed in at most n·m·rk(𝓑) iterations → every run is bounded (clause 1), every stopped run returns an enforceable B′ with C(B′) ≤ C(B) (clause 2), every unstopped run can continue (clause 3), and such a run exists (clause 4); reason: the proof does not depend on the choices made; clause 4 is the paper's statement.
--   - generalization: iterations of the while-loop in Algorithm 1 → both the iterations of the while-loop of Line 2 and the total number of exchanges (iterations of Lines 3–5 and of the while-loop of Line 7) are at most n·m·rk(𝓑); reason: the phrase does not say which of the two loops is counted; the exchange count is at least the Line-2 count, and both are bounded, so either reading is covered.
--   - encoding: Algorithm 1 as pseudocode → a nondeterministic transition system on states (profile, control point: Line 2 or the loop of Line 7 on e), one exchange per transition; a run is a sequence s₀,…,s_k from (B, Line 2); reason: Lean convention for a nondeterministic algorithm; the transitions are exactly Lines 3–5 and the iterations of Lines 7–10, with control returning to Line 2 when (2) fails on e.
--   - correction: condition (2) tested for every e ∈ E → condition (2) tested only for resources e with Nₑ(B) ≠ ∅; reason: as printed it fails when cₑ(∅) > 0, e.g. fixed costs (p.6): one player, uniform rank-1 matroid on {e, f}, cₑ ≡ c_f ≡ 1, d ≡ 0, B₁ = {f}: B is enforceable but (D2) at e reads 1 ≤ 0, condition (2) holds at e, and Line 8 must pick a player from Nₑ(B) = ∅.
--   - reading: minimum over f ∈ E with Bᵢ + f − e ∈ 𝓑ᵢ (in Δᵉᵢ(B) and Δ̄ᵉᵢ(B)) → Bᵢ + f − e is (Bᵢ ∖ {e}) ∪ {f}, so f = e is admissible and the minimum is over a nonempty finite set whenever e ∈ Bᵢ; reason: literal index set; excluding f = e instead gives the same (D1) ∧ (D2), Algorithm 1 never selects f = e, and this reading needs no value +∞.
--   - reading: Definition 2 (budget balance cₑ = Σ_{i∈Nₑ(S)} ξᵢ,ₑ(S)) written for fixed costs cₑ → budget balance cₑ(Nₑ(S)) = Σ_{i∈Nₑ(S)} ξᵢ,ₑ(S) for the set-function costs of §3; reason: §3 replaces cₑ by cₑ(Nₑ(S)) (cₑ(B) := cₑ(Nₑ(B)), p.6); the only reading under which Lemma 3 is meaningful.
--   - encoding: finite sets N of players and E of resources; base families 𝓑ᵢ of matroids (Eᵢ, 𝓑ᵢ) → finite types N, E; Mathlib Matroid E with ground set Eᵢ; a profile is a map N → Finset E whose i-th value is a base; reason: Lean convention; same instances.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Theorem 5, p.7 (proof pp.7–8)

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Protocol
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

namespace SepCostShare

/-- **Theorem 5**, Harks, Hoefer, Huber & Surek, *Efficient Black-Box Reductions for Separable Cost
Sharing*, arXiv:1802.10351v1, p.7: "Let B be a strategy profile for a matroid congestion model with
subadditive costs. There is an enforceable strategy B′ with C(B′) ≤ C(B) that can be computed in at
most n·m·rk(𝓑) iterations of the while-loop in Algorithm 1, where rk(𝓑) = max_{i∈N} rkᵢ."

For every matroid game with subadditive costs and every profile `B`, with `n = |N|`, `m = |E|`:

1. every run of Algorithm 1 from `B` (any choice of resource, player and minimizer) performs at
   most `n·m·rk(𝓑)` iterations of the while-loop of Line 2 and at most `n·m·rk(𝓑)` exchanges in
   total (iterations of Lines 3–5 plus iterations of the loop of Line 7);
2. every run that stops (back at Line 2 with no resource satisfying (1) or (2)) returns an
   enforceable profile `B′` with `C(B′) ≤ C(B)`;
3. Algorithm 1 is well defined: every run either has stopped or can perform a further step;
4. some run from `B` stops after at most `n·m·rk(𝓑)` exchanges with an enforceable `B′` and
   `C(B′) ≤ C(B)`. -/
theorem theorem_5 {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E) (hB : G.IsProfile B) :
    (∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
        G.outerIters s k ≤ Fintype.card N * Fintype.card E * G.rkMax ∧
          k ≤ Fintype.card N * Fintype.card E * G.rkMax) ∧
      (∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
        (s k).2 = none → G.Stopped (s k).1 →
          G.Enforceable (s k).1 ∧ G.cost (s k).1 ≤ G.cost B) ∧
      (∀ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k →
        ((s k).2 = none ∧ G.Stopped (s k).1) ∨ ∃ y, G.AlgStep (s k) y) ∧
      (∃ (s : ℕ → (N → Finset E) × Option E) (k : ℕ), G.IsRun B s k ∧ (s k).2 = none ∧
        G.Stopped (s k).1 ∧ k ≤ Fintype.card N * Fintype.card E * G.rkMax ∧
        G.Enforceable (s k).1 ∧ G.cost (s k).1 ≤ G.cost B) := by sorry

end SepCostShare
