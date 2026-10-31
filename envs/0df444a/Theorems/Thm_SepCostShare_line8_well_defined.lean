-- Prove2me | Theorems.Thm_SepCostShare_line8_well_defined
-- name    : SepCostShare.line8_well_defined
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:42.562623+00:00
-- url     : https://prove2.me/theorems/b1a8182e-de70-40b2-931b-104fb336d38a
-- title:
--   Theorem 5, proof — Line 8 of Algorithm 1 is well defined (corrected: used resources)
-- statement:
--   Let $\mathcal M$ be a matroid game with subadditive costs, $B'$ a profile and $e$ a resource with $N_e(B')\ne\emptyset$ and
--   $$c_e(B')>\sum_{i\in N_e(B')}\bigl(\bar\Delta^e_i(B')-d_{i,e}\bigr).$$
--   Then there is a player $i\in N_e(B')$ with
--   $$c_e(\{i\})+d_{i,e}>\bar\Delta^e_i(B').$$
--
--   This is what Line 8 of Algorithm 1 needs: whenever the loop of Line 7 runs on $e$, a player with $\pi^e_i>\bar\Delta^e_i(B')$ exists.
--
--   Differences from the source:
--   - correction: the claim (whenever cₑ(B′) > Σ_{i∈Nₑ(B′)} (Δ̄ᵉᵢ(B′) − dᵢ,ₑ) there is such an i) stated for every e ∈ E → the claim (whenever cₑ(B′) > Σ_{i∈Nₑ(B′)} (Δ̄ᵉᵢ(B′) − dᵢ,ₑ) there is such an i) stated only for resources e with Nₑ(B) ≠ ∅; reason: as printed it fails when cₑ(∅) > 0, e.g. fixed costs (p.6): one player, uniform rank-1 matroid on {e, f}, cₑ ≡ c_f ≡ 1, d ≡ 0, B₁ = {f}: B is enforceable but (D2) at e reads 1 ≤ 0, condition (2) holds at e, and Line 8 must pick a player from Nₑ(B) = ∅.
--   - reading: minimum over f ∈ E with Bᵢ + f − e ∈ 𝓑ᵢ (in Δᵉᵢ(B) and Δ̄ᵉᵢ(B)) → Bᵢ + f − e is (Bᵢ ∖ {e}) ∪ {f}, so f = e is admissible and the minimum is over a nonempty finite set whenever e ∈ Bᵢ; reason: literal index set; excluding f = e instead gives the same (D1) ∧ (D2), Algorithm 1 never selects f = e, and this reading needs no value +∞.
--   - encoding: finite sets N of players and E of resources; base families 𝓑ᵢ of matroids (Eᵢ, 𝓑ᵢ) → finite types N, E; Mathlib Matroid E with ground set Eᵢ; a profile is a map N → Finset E whose i-th value is a base; reason: Lean convention; same instances.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Theorem 5, proof, p.7, "To show that the algorithm is well-defined, we only need to check Line 8"

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

namespace SepCostShare

/-- **Theorem 5, proof, p.7** (arXiv:1802.10351v1), Line 8 of Algorithm 1 is well defined: "By
subadditivity we get Σ_{i∈Nₑ(B′)} cₑ({i}) ≥ cₑ(B′). Thus, whenever
cₑ(B′) > Σ_{i∈Nₑ(B′)} (Δ̄ᵉᵢ(B′) − dᵢ,ₑ), there is an i ∈ Nₑ(B′) with cₑ({i}) + dᵢ,ₑ > Δ̄ᵉᵢ(B′)."

Here condition (2) on `e` includes `Nₑ(B′) ≠ ∅` (see `MatroidGame.cond2`). -/
theorem line8_well_defined {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (hB : G.IsProfile B) (e : E) (h2 : G.cond2 B e) :
    ∃ i ∈ G.users e B, G.deltaBar B i e < G.c e {i} + G.d i e := by sorry

end SepCostShare
