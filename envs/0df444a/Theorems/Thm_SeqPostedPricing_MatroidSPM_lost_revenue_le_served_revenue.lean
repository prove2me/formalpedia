-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_lost_revenue_le_served_revenue
-- name    : SeqPostedPricing.MatroidSPM.lost_revenue_le_served_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:44:35.493161+00:00
-- url     : https://prove2.me/theorems/ae8ab663-dbef-4821-8986-60dfedfff6ec
-- title:
--   Proof of Thm 5: revenue lost to blocked agents $\le$ revenue obtained (corrected: blocked agents of $B_j$; final sum to $\ell$)
-- statement:
--   Let $\mathcal J$ be a matroid, let $q_1,\dots,q_n\ge0$ satisfy
--
--   $$
--   \sum_{i\in T}q_i\le\mathrm{rank}(T)\quad\text{for every }T\subseteq[n],
--   $$
--
--   and run the SPM with prices that are nonnegative on the agents it makes offers to and non-increasing along the order $\sigma$ on those agents. Then for every value profile $\mathbf v$, with $S$ the set of agents served,
--
--   $$
--   \sum_{i\ \text{blocked}}p_i\,q_i\ \le\ \sum_{i\in S}p_i ,
--   $$
--
--   where an agent is blocked if the SPM would make it an offer but its addition to the agents served before it is infeasible. In the proof of Theorem 5 this is the bound "revenue lost $\le$ revenue obtained", given that $S$ is served.
--
--   Differences from the source:
--   - correction: Σ_{1≤j≤ℓ} Σ_{i∈B_j} p_i q_i, a sum over all of B_j = span(S_j) \ span(S_{j−1}) → the sum over the blocked agents only; reason: over all of B_j the display is false: one item (1-uniform matroid), prices (1, ½), q = (½, ½), agent 1 rejects and agent 2 accepts; S = {2}, B_1 = {1, 2}, Σ_{B_1} p_i q_i = ¾ > ½ = revenue obtained; the paper's sentence "B_j partition the set of blocked agents" intends the blocked part
--   - correction: … = Σ_{1≤j<ℓ} p^j, "the revenue obtained by serving S" → Σ_{i∈S} p_i = Σ_{1≤j≤ℓ} p^j; reason: Σ_{1≤j<ℓ}(p^j − p^{j+1})·j + p^ℓ·ℓ telescopes to Σ_{1≤j≤ℓ} p^j; for ℓ = 1 the printed sum is empty (0) while the previous line is p^1
--   - generalization: q_i = q_i^M and p_i = F_i^{−1}(1 − q_i) of Myerson's mechanism, offers to every agent → any q ≥ 0 with Σ_{i∈T} q_i ≤ rank(T) for all T, any set of agents offered to, prices ≥ 0 on it and non-increasing along σ; reason: Myerson's q satisfy the rank bound (rank_bound) and its prices are ≥ 0 (an optimal mechanism serves an agent only where its virtual value is ≥ 0, and v ≥ φ(v)); the display's last step multiplies Σ q ≤ ℓ by p^ℓ, which uses p^ℓ ≥ 0
--   - encoding: expected revenue lost given that S is served → a pointwise inequality for every value profile v; reason: conditioning on S fixes the run; the inequality holds for each run
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 5, display, p. 7

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsMatroid
import Definitions.Def_SeqPostedPricing_MatroidSPM_rank
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmOffered
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsDecreasingOrder
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **The revenue lost to blocked agents is at most the revenue obtained (corrected display of
the proof of Theorem 5).**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4.1, proof of Theorem 5, display, p. 7 (PDF p. 9): "Denote the price offered to agent ij by
p^j. Then, the expected revenue lost given that S is served is Σ_{1≤j≤ℓ} Σ_{i∈Bj} pi qi ≤ …
≤ Σ_{1≤j<ℓ} (p^j − p^{j+1}) · j + p^ℓ · ℓ = Σ_{1≤j<ℓ} p^j, which is the revenue obtained by
serving S. Here we used Σ_{i∈span(Sj)} qi ≤ rank(Sj) ≤ |Sj| = j."

Let `J` be a matroid, `q ≥ 0` numbers with `Σ_{i∈T} q_i ≤ rank(T)` for every set `T`, and prices
that are nonnegative on the active agents and non-increasing along the order `σ`. Then for every
value profile `v`, the sum of `p_i q_i` over the blocked agents (active agents not offered
service) is at most the sum of the prices of the agents served by the SPM.

**Formalization Note.** Two corrections of the printed display: the sums over `B_j` range over
the blocked agents of `B_j` (over all of `B_j` the display is false), and the final sum runs over
`1 ≤ j ≤ ℓ`, the revenue of serving `S` (the printed `j < ℓ` is empty for `ℓ = 1`). Stated
pointwise in `v` (the paper conditions on the served set `S`) and for any `q` with the rank
bound. -/
theorem lost_revenue_le_served_revenue {n : ℕ} (Feas : Finset (Fin n) → Prop)
    (hmat : IsMatroid Feas) (p q : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n)
    (hσ : IsDecreasingOrder p active σ) (hp0 : ∀ i ∈ active, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hrank : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (rank Feas T : ℝ)) (v : Fin n → ℝ) :
    ∑ t ∈ Finset.univ.filter (fun t => σ t ∈ active ∧ ¬ spmOffered Feas p active σ v t),
        p (σ t) * q (σ t)
      ≤ ∑ i ∈ spmServedBefore Feas p active σ v n, p i := by sorry

end SeqPostedPricing.MatroidSPM
