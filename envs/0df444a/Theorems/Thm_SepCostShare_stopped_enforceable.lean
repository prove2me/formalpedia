-- Prove2me | Theorems.Thm_SepCostShare_stopped_enforceable
-- name    : SepCostShare.stopped_enforceable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:54.14999+00:00
-- url     : https://prove2.me/theorems/f7746578-fd0a-4cd7-9ba0-35a7fb5db1a9
-- title:
--   Theorem 5, proof — $0\le\bar\Delta^e_i(B)\le\Delta^e_i(B)$, and a profile where Algorithm 1 stops is enforceable (corrected: (2) on used resources)
-- statement:
--   Let $\mathcal M$ be a matroid game with subadditive costs and $B$ a profile. Then
--
--   1. $0\le\bar\Delta^e_i(B)\le\Delta^e_i(B)$ for all $i\in N$ and $e\in E$;
--   2. if no resource satisfies condition (1) or condition (2) of Algorithm 1 at $B$, then $B$ is enforceable.
--
--   So (D1) and (D2) of Lemma 3 already hold when they hold for the smaller values $\bar\Delta$, and whenever Algorithm 1 terminates its output is enforceable.
--
--   Differences from the source:
--   - generalization: if the algorithm terminates, the resulting profile B′ will be enforceable → every profile at which no resource satisfies (1) or (2) is enforceable; reason: a terminating run stops exactly at such a profile, so this specializes to the paper's claim.
--   - correction: condition (2) tested for every e ∈ E → condition (2) tested only for resources e with Nₑ(B) ≠ ∅; reason: as printed it fails when cₑ(∅) > 0, e.g. fixed costs (p.6): one player, uniform rank-1 matroid on {e, f}, cₑ ≡ c_f ≡ 1, d ≡ 0, B₁ = {f}: B is enforceable but (D2) at e reads 1 ≤ 0, condition (2) holds at e, and Line 8 must pick a player from Nₑ(B) = ∅.
--   - reading: minimum over f ∈ E with Bᵢ + f − e ∈ 𝓑ᵢ (in Δᵉᵢ(B) and Δ̄ᵉᵢ(B)) → Bᵢ + f − e is (Bᵢ ∖ {e}) ∪ {f}, so f = e is admissible and the minimum is over a nonempty finite set whenever e ∈ Bᵢ; reason: literal index set; excluding f = e instead gives the same (D1) ∧ (D2), Algorithm 1 never selects f = e, and this reading needs no value +∞.
--   - reading: Definition 2 (budget balance cₑ = Σ_{i∈Nₑ(S)} ξᵢ,ₑ(S)) written for fixed costs cₑ → budget balance cₑ(Nₑ(S)) = Σ_{i∈Nₑ(S)} ξᵢ,ₑ(S) for the set-function costs of §3; reason: §3 replaces cₑ by cₑ(Nₑ(S)) (cₑ(B) := cₑ(Nₑ(B)), p.6); the only reading under which Lemma 3 is meaningful.
--   - encoding: finite sets N of players and E of resources; base families 𝓑ᵢ of matroids (Eᵢ, 𝓑ᵢ) → finite types N, E; Mathlib Matroid E with ground set Eᵢ; a profile is a map N → Finset E whose i-th value is a base; reason: Lean convention; same instances.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Theorem 5, proof, p.7, "First, observe that if (D1) and (D2) from Lemma 3 hold true for smaller values"

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Protocol
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

namespace SepCostShare

/-- **Theorem 5, proof, p.7** (arXiv:1802.10351v1): "First, observe that if (D1) and (D2) from
Lemma 3 hold true for smaller values 0 ≤ Δ̄ᵉᵢ(B) ≤ Δᵉᵢ(B), i ∈ N, e ∈ E, then the profile B is
also enforceable. Hence, if the algorithm terminates, the resulting strategy profile B′ will be
enforceable."

Two conclusions for every profile `B` of a matroid game with subadditive costs:
(i) `0 ≤ Δ̄ᵉᵢ(B) ≤ Δᵉᵢ(B)` for all `i ∈ N`, `e ∈ E`;
(ii) if the while-loop of Algorithm 1 stops at `B` (no resource satisfies (1) or (2)), then `B`
is enforceable. -/
theorem stopped_enforceable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (hB : G.IsProfile B) :
    (∀ (i : N) (e : E), 0 ≤ G.deltaBar B i e ∧ G.deltaBar B i e ≤ G.delta B i e) ∧
      (G.Stopped B → G.Enforceable B) := by sorry

end SepCostShare
