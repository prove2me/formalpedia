-- Prove2me | Theorems.Thm_SepCostShare_type1_cost_decrease
-- name    : SepCostShare.type1_cost_decrease
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:54.889551+00:00
-- url     : https://prove2.me/theorems/fd02546a-d7a9-4090-8f47-970170b62ad6
-- title:
--   Theorem 5, proof — a type-(1) exchange decreases the total cost: $C(B')-C(B)\le\bar\Delta^e_i(B)-d_{i,e}<0$
-- statement:
--   Let $\mathcal M$ be a matroid game with subadditive costs, $B$ a profile, $e$ a resource and $i\in N_e(B)$ with
--   $$d_{i,e}>\bar\Delta^e_i(B)$$
--   (condition (1)). Let $f_i\in\arg\min_{f\in E,\ B_i+f-e\in\mathcal B_i}\pi^f_i$ and $B'=(B_i+f_i-e,B_{-i})$. Then
--   $$C(B')-C(B)\le\bar\Delta^e_i(B)-d_{i,e}<0 .$$
--
--   So every iteration of Lines 3–5 of Algorithm 1 strictly lowers the total cost.
--
--   Differences from the source:
--   - reading: minimum over f ∈ E with Bᵢ + f − e ∈ 𝓑ᵢ (in Δᵉᵢ(B) and Δ̄ᵉᵢ(B)) → Bᵢ + f − e is (Bᵢ ∖ {e}) ∪ {f}, so f = e is admissible and the minimum is over a nonempty finite set whenever e ∈ Bᵢ; reason: literal index set; excluding f = e instead gives the same (D1) ∧ (D2), Algorithm 1 never selects f = e, and this reading needs no value +∞.
--   - encoding: finite sets N of players and E of resources; base families 𝓑ᵢ of matroids (Eᵢ, 𝓑ᵢ) → finite types N, E; Mathlib Matroid E with ground set Eᵢ; a profile is a map N → Finset E whose i-th value is a base; reason: Lean convention; same instances.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Theorem 5, proof, p.8, "Consider first a packet movement of type (1)"

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

namespace SepCostShare

/-- **Theorem 5, proof, p.8** (arXiv:1802.10351v1), a packet movement of type (1) decreases the
total cost: "Let B and B′ be the profiles before and after packet iₖ has been moved from e to fᵢ
[…] C(B′) − C(B) = (c_{fᵢ}(B′) − c_{fᵢ}(B) + dᵢ,fᵢ) − (cₑ(B) − cₑ(B′) + dᵢ,ₑ) ≤ c_{fᵢ}({i}) +
dᵢ,fᵢ − (cₑ(B) − cₑ(B′) + dᵢ,ₑ) = Δ̄ᵉᵢ(B) − dᵢ,ₑ + (cₑ(B′) − cₑ(B)) ≤ Δ̄ᵉᵢ(B) − dᵢ,ₑ < 0."

For a profile `B`, a player `i ∈ Nₑ(B)` with `dᵢ,ₑ > Δ̄ᵉᵢ(B)` (condition (1)) and a minimizer
`fᵢ` of Line 4: `C(Bᵢ + fᵢ − e, B₋ᵢ) − C(B) ≤ Δ̄ᵉᵢ(B) − dᵢ,ₑ < 0`. -/
theorem type1_cost_decrease {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (hB : G.IsProfile B) (i : N) (e f : E) (hi : i ∈ G.users e B)
    (h1 : G.deltaBar B i e < G.d i e) (hf : G.IsArgmin B i e f) :
    G.cost (G.swap B i e f) - G.cost B ≤ G.deltaBar B i e - G.d i e ∧
      G.deltaBar B i e - G.d i e < 0 := by sorry

end SepCostShare
