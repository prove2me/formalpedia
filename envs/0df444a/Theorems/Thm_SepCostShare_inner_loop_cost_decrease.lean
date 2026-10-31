-- Prove2me | Theorems.Thm_SepCostShare_inner_loop_cost_decrease
-- name    : SepCostShare.inner_loop_cost_decrease
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:00.549826+00:00
-- url     : https://prove2.me/theorems/fc10099a-b9c1-474d-9ac1-b4f0d28c9518
-- title:
--   Theorem 5, proof, (3)–(5) — one complete run of the inner while-loop decreases the total cost (corrected: used resources)
-- statement:
--   Let $\mathcal M$ be a matroid game with subadditive costs, $B$ a profile and $e$ a resource. Suppose that $B'$ is obtained from $B$ by one or more iterations of the loop of Lines 7–10 of Algorithm 1 on $e$: in each iteration condition (2) holds on $e$ at the current profile $X$, a player $i\in N_e(X)$ with $\pi^e_i>\bar\Delta^e_i(X)$ is picked, and $X_i$ is replaced by $X_i+f_i-e$ for a minimizer $f_i$ of $\pi^f_i$ over the admissible $f$. Suppose further that (2) no longer holds on $e$ at $B'$, so that the loop exits. Then
--   $$C(B')<C(B).$$
--
--   Together with the type-(1) case this shows that the profile returned by Algorithm 1 costs no more than its input.
--
--   Differences from the source:
--   - generalization: the loop of Line 7 entered from Line 6, i.e. after (1) failed on e → any run of the loop of Lines 7–10 on e, whether or not (1) holds on e at its start; reason: the cost argument never uses the failure of (1); the statement specializes to runs entered from Line 6.
--   - correction: condition (2) tested (and the loop exits when it fails) for every e ∈ E → condition (2) tested (and the loop exits when it fails) only for resources e with Nₑ(B) ≠ ∅; reason: as printed it fails when cₑ(∅) > 0, e.g. fixed costs (p.6): one player, uniform rank-1 matroid on {e, f}, cₑ ≡ c_f ≡ 1, d ≡ 0, B₁ = {f}: B is enforceable but (D2) at e reads 1 ≤ 0, condition (2) holds at e, and Line 8 must pick a player from Nₑ(B) = ∅.
--   - reading: minimum over f ∈ E with Bᵢ + f − e ∈ 𝓑ᵢ (in Δᵉᵢ(B) and Δ̄ᵉᵢ(B)) → Bᵢ + f − e is (Bᵢ ∖ {e}) ∪ {f}, so f = e is admissible and the minimum is over a nonempty finite set whenever e ∈ Bᵢ; reason: literal index set; excluding f = e instead gives the same (D1) ∧ (D2), Algorithm 1 never selects f = e, and this reading needs no value +∞.
--   - encoding: finite sets N of players and E of resources; base families 𝓑ᵢ of matroids (Eᵢ, 𝓑ᵢ) → finite types N, E; Mathlib Matroid E with ground set Eᵢ; a profile is a map N → Finset E whose i-th value is a base; reason: Lean convention; same instances.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Theorem 5, proof, p.8, (3)–(5), "Now consider packet movements of type (2)"

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

namespace SepCostShare

/-- **Theorem 5, proof, p.8, (3)–(5)** (arXiv:1802.10351v1), packet movements of type (2): "We
treat all movements occurring in one run of the while loop in Line 7. Let B denote the profile
before and B′ after all these movements. […] C(B′) − C(B) = […] < 0."

For a profile `B` and a resource `e`, if `B′` is reached from `B` by one or more iterations of the
loop of Lines 7–10 on `e` and (2) no longer holds on `e` at `B′` (the loop exits), then
`C(B′) < C(B)`. -/
theorem inner_loop_cost_decrease {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B B' : N → Finset E)
    (hB : G.IsProfile B) (e : E) (hrun : Relation.TransGen (G.InnerStep e) B B')
    (hexit : ¬ G.cond2 B' e) :
    G.cost B' < G.cost B := by sorry

end SepCostShare
