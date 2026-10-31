-- Prove2me | Theorems.Thm_SepCostShare_exchange_pi_decrease
-- name    : SepCostShare.exchange_pi_decrease
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:51.273981+00:00
-- url     : https://prove2.me/theorems/d71f1001-6310-42d6-9161-9b88f3d9d29f
-- title:
--   Theorem 5, proof — every exchange of Algorithm 1 strictly decreases the virtual value: $\pi^e_i>\pi^{f_i}_i$
-- statement:
--   Let $\mathcal M$ be a matroid game with subadditive costs, $B$ a profile, $e$ a resource and $i\in N_e(B)$ a player selected as in Line 3 of Algorithm 1 ($d_{i,e}>\bar\Delta^e_i(B)$) or as in Line 8 ($\pi^e_i>\bar\Delta^e_i(B)$). Let
--   $$f_i\in\arg\min_{f\in E,\ B_i+f-e\in\mathcal B_i}\pi^f_i.$$
--   Then
--   $$\pi^e_i>\pi^{f_i}_i;$$
--   moreover $f_i\notin B_i$, and $(B_i+f_i-e,B_{-i})$ is again a profile.
--
--   So every exchange performed in Line 5 or Line 10 moves a "packet" of player $i$ to a resource of strictly smaller virtual value.
--
--   Differences from the source:
--   - generalization: packet movements executed in Line 5 or Line 10 of a run of Algorithm 1 → any profile, any player i ∈ Nₑ(B) with dᵢ,ₑ > Δ̄ᵉᵢ(B) or πᵉᵢ > Δ̄ᵉᵢ(B), and any minimizer fᵢ; reason: every exchange of Lines 5 and 10 has this form, so the statement specializes to them.
--   - generalization: conclusion πᵉᵢ > π^{fᵢ}ᵢ → πᵉᵢ > π^{fᵢ}ᵢ, and in addition fᵢ ∉ Bᵢ and (Bᵢ + fᵢ − e, B₋ᵢ) is a profile; reason: added conclusions that the run relies on; dropping them gives the paper's claim.
--   - reading: minimum over f ∈ E with Bᵢ + f − e ∈ 𝓑ᵢ (in Δᵉᵢ(B) and Δ̄ᵉᵢ(B)) → Bᵢ + f − e is (Bᵢ ∖ {e}) ∪ {f}, so f = e is admissible and the minimum is over a nonempty finite set whenever e ∈ Bᵢ; reason: literal index set; excluding f = e instead gives the same (D1) ∧ (D2), Algorithm 1 never selects f = e, and this reading needs no value +∞.
--   - encoding: finite sets N of players and E of resources; base families 𝓑ᵢ of matroids (Eᵢ, 𝓑ᵢ) → finite types N, E; Mathlib Matroid E with ground set Eᵢ; a profile is a map N → Finset E whose i-th value is a base; reason: Lean convention; same instances.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Theorem 5, proof, p.7, "For a packet movement executed in Line 5 of Algorithm 1" … "In both cases we obtain πᵉᵢ > π^{fᵢ}ᵢ"

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

namespace SepCostShare

/-- **Theorem 5, proof, p.7** (arXiv:1802.10351v1): every exchange of Algorithm 1 moves to a
resource of strictly smaller virtual value. "For a packet movement executed in Line 5 of
Algorithm 1, we have dᵢ,ₑ > Δ̄ᵉᵢ(B′) […] For packet movements executed in Line 10, then by the
choice of player i ∈ Nₑ(B′) (see Line 8) […] it holds πᵉᵢ > Δ̄ᵉᵢ(B′) = π^{fᵢ}ᵢ. In both cases we
obtain πᵉᵢ > π^{fᵢ}ᵢ."

For a profile `B`, a player `i ∈ Nₑ(B)` selected as in Line 3 (`dᵢ,ₑ > Δ̄ᵉᵢ(B)`) or as in Line 8
(`πᵉᵢ > Δ̄ᵉᵢ(B)`), and `fᵢ` a minimizer of Lines 4/9: `π^{fᵢ}ᵢ < πᵉᵢ`; moreover `fᵢ ∉ Bᵢ` and the
updated profile `(Bᵢ + fᵢ − e, B₋ᵢ)` is again a profile. -/
theorem exchange_pi_decrease {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (hB : G.IsProfile B) (i : N) (e f : E) (hi : i ∈ G.users e B)
    (hsel : G.deltaBar B i e < G.d i e ∨ G.deltaBar B i e < G.pi i e)
    (hf : G.IsArgmin B i e f) :
    G.pi i f < G.pi i e ∧ f ∉ B i ∧ G.IsProfile (G.swap B i e f) := by sorry

end SepCostShare
