-- Prove2me | Theorems.Thm_SepCostShare_exchange_count
-- name    : SepCostShare.exchange_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:53.041999+00:00
-- url     : https://prove2.me/theorems/4089afe8-035e-4d61-9fac-9d653d2ee215
-- title:
--   Theorem 5, proof — strictly $\pi$-decreasing exchanges number at most $\sum_{i}\mathrm{rk}_i(m-1)\le n\cdot m\cdot\mathrm{rk}(\mathcal B)$
-- statement:
--   Let $\mathcal M$ be a matroid game with subadditive costs, $n=|N|$ and $m=|E|$. Let $B^0,B^1,\dots,B^k$ be profiles such that each $B^{t+1}$ arises from $B^t$ by a single exchange of one player, $B^{t+1}=(B^t_i+f-e,B^t_{-i})$ with $e\in B^t_i$, $f\notin B^t_i$ and
--   $$\pi^f_i<\pi^e_i .$$
--   Then
--   $$k\le\sum_{i\in N}\mathrm{rk}_i\cdot(m-1)\le n\cdot m\cdot\mathrm{rk}(\mathcal B).$$
--
--   Since $\pi^e_i$ does not depend on the profile, each of the $\mathrm{rk}_i$ "packets" of player $i$ can take at most $m$ different virtual values and so move at most $m-1$ times. With the strict decrease of every exchange of Algorithm 1, this bounds its running time.
--
--   Differences from the source:
--   - generalization: the packet movements of a run of Algorithm 1 → any sequence of profiles in which every step is one exchange to a resource of strictly smaller virtual value; reason: every exchange of Algorithm 1 is such a step (Lines 5 and 10, by the strict decrease of π), so the bound specializes to the algorithm.
--   - encoding: m − 1 and rkᵢ → natural-number subtraction m − 1; rkᵢ is the natural-number value of Mathlib's eRank of 𝓜ᵢ; reason: m − 1 is truncated only at m = 0, where every rkᵢ is 0 as well; eRank is finite for a finite ground set and equals the size of every base.
--   - encoding: finite sets N of players and E of resources; base families 𝓑ᵢ of matroids (Eᵢ, 𝓑ᵢ) → finite types N, E; Mathlib Matroid E with ground set Eᵢ; a profile is a map N → Finset E whose i-th value is a base; reason: Lean convention; same instances.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Theorem 5, proof, p.8, "Note that the virtual cost value πᵉᵢ does not depend on the profile B" … "Σ_{i∈N} rkᵢ·(m − 1) ≤ n·m·rk(𝓑)"

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation

namespace SepCostShare

/-- **Theorem 5, proof, p.8** (arXiv:1802.10351v1), counting packet movements: "Note that the
virtual cost value πᵉᵢ does not depend on the profile B. Thus, there are at most m different
virtual cost values that a packet iₖ of player i can experience, and thus packet iₖ can move at
most m − 1 times. The following is an upper bound on the total number of packet movements for all
players Σ_{i∈N} rkᵢ·(m − 1) ≤ n·m·rk(𝓑)."

Stated for any sequence of profiles `B⁰, B¹, …, Bᵏ` of a matroid game with subadditive costs in
which every step is a single exchange `Bᵗ⁺¹ = (Bᵗᵢ + f − e, Bᵗ₋ᵢ)` with `e ∈ Bᵗᵢ`, `f ∉ Bᵗᵢ` and
`πᶠᵢ < πᵉᵢ`: then `k ≤ Σ_{i∈N} rkᵢ·(m − 1) ≤ n·m·rk(𝓑)`, where `n = |N|`, `m = |E|`.

**Formalization Note.** `m − 1` is natural-number subtraction; it is `0` only when `m = 0`, in
which case every `rkᵢ` is `0` as well. -/
theorem exchange_count {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (s : ℕ → (N → Finset E)) (k : ℕ)
    (hs0 : G.IsProfile (s 0))
    (hstep : ∀ t < k, G.IsProfile (s (t + 1)) ∧
      ∃ (i : N) (e f : E), e ∈ s t i ∧ f ∉ s t i ∧ G.pi i f < G.pi i e ∧
        s (t + 1) = G.swap (s t) i e f) :
    k ≤ ∑ i : N, G.rank i * (Fintype.card E - 1) ∧
      ∑ i : N, G.rank i * (Fintype.card E - 1) ≤
        Fintype.card N * Fintype.card E * G.rkMax := by sorry

end SepCostShare
