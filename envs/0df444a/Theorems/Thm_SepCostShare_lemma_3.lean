-- Prove2me | Theorems.Thm_SepCostShare_lemma_3
-- name    : SepCostShare.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:46.083985+00:00
-- url     : https://prove2.me/theorems/5e9b8b31-3208-4710-93e5-7ebd1d10ee60
-- title:
--   Lemma 3 — $B$ is enforceable iff (D1) and (D2) (corrected: (D2) on used resources)
-- statement:
--   Let $\mathcal M$ be a matroid game with subadditive costs and $B=(B_1,\dots,B_n)$ a profile. Then $B$ is enforceable by a separable protocol if and only if
--
--   1. (D1) $d_{i,e}\le\Delta^e_i(B)$ for all $i\in N$ and $e\in B_i$, and
--   2. (D2) for every resource $e$ with $N_e(B)\ne\emptyset$,
--   $$c_e(B)\le\sum_{i\in N_e(B)}\bigl(\Delta^e_i(B)-d_{i,e}\bigr).$$
--
--   (D1) implies that each summand in (D2) is nonnegative. The characterization is due to Harks and von Falkenhausen; the paper notes that its proof also works for subadditive costs. Its "if" direction is the first step of the proof of Theorem 5.
--
--   Differences from the source:
--   - correction: (D2) required for every e ∈ E → (D2) required only for resources e with Nₑ(B) ≠ ∅; reason: as printed it fails when cₑ(∅) > 0, e.g. fixed costs (p.6): one player, uniform rank-1 matroid on {e, f}, cₑ ≡ c_f ≡ 1, d ≡ 0, B₁ = {f}: B is enforceable but (D2) at e reads 1 ≤ 0, condition (2) holds at e, and Line 8 must pick a player from Nₑ(B) = ∅.
--   - reading: minimum over f ∈ E with Bᵢ + f − e ∈ 𝓑ᵢ (in Δᵉᵢ(B) and Δ̄ᵉᵢ(B)) → Bᵢ + f − e is (Bᵢ ∖ {e}) ∪ {f}, so f = e is admissible and the minimum is over a nonempty finite set whenever e ∈ Bᵢ; reason: literal index set; excluding f = e instead gives the same (D1) ∧ (D2), Algorithm 1 never selects f = e, and this reading needs no value +∞.
--   - reading: Definition 2 (budget balance cₑ = Σ_{i∈Nₑ(S)} ξᵢ,ₑ(S)) written for fixed costs cₑ → budget balance cₑ(Nₑ(S)) = Σ_{i∈Nₑ(S)} ξᵢ,ₑ(S) for the set-function costs of §3; reason: §3 replaces cₑ by cₑ(Nₑ(S)) (cₑ(B) := cₑ(Nₑ(B)), p.6); the only reading under which Lemma 3 is meaningful.
--   - encoding: finite sets N of players and E of resources; base families 𝓑ᵢ of matroids (Eᵢ, 𝓑ᵢ) → finite types N, E; Mathlib Matroid E with ground set Eᵢ; a profile is a map N → Finset E whose i-th value is a base; reason: Lean convention; same instances.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Lemma 3, (D1), (D2), p.6 (cited from [36]; footnote 1, p.6)

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Protocol
import Definitions.Def_SepCostShare_Deviation

namespace SepCostShare

/-- **Lemma 3**, Harks, Hoefer, Huber & Surek, arXiv:1802.10351v1, p.6 (cited from [36]; footnote 1:
"the proof also works for subadditive cost functions"): a collection of bases `B` is enforceable by
a separable protocol if and only if
`dᵢ,ₑ ≤ Δᵉᵢ(B)` for all `i ∈ N`, `e ∈ Bᵢ` (D1), and
`cₑ(B) ≤ Σ_{i∈Nₑ(B)} (Δᵉᵢ(B) − dᵢ,ₑ)` for all `e ∈ E` with `Nₑ(B) ≠ ∅` (D2).

**Formalization Note.** (D2) is required only for resources used in `B` (correction: as printed,
"for all e ∈ E", it reads `cₑ(∅) ≤ 0` at an unused resource, which fails for fixed costs
`cₑ > 0` although such profiles can be enforceable). The minimum in `Δᵉᵢ(B)` admits `f = e`. -/
theorem lemma_3 {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E) (hB : G.IsProfile B) :
    G.Enforceable B ↔
      (∀ (i : N) (e : E), e ∈ B i → G.d i e ≤ G.delta B i e) ∧
        (∀ e : E, (G.users e B).Nonempty →
          G.c e (G.users e B) ≤ ∑ i ∈ G.users e B, (G.delta B i e - G.d i e)) := by sorry

end SepCostShare
