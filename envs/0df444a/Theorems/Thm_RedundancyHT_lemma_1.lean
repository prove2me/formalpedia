-- Prove2me | Theorems.Thm_RedundancyHT_lemma_1
-- name    : RedundancyHT.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:51.25312+00:00
-- url     : https://prove2.me/theorems/8526054f-d78b-4925-932f-91e206e7ec03
-- title:
--   Lemma 1, (42), p.34: the servers of $\mathcal T^*$ are all busy in the limit
-- statement:
--   Let $\mathcal T^*$ be the critical subset, and let $\mathbb P_{\mathrm{c.o.s.}}(u)$ be the stationary probability that precisely the servers in the vector $u$ are idle, $u_l$ being the $l$th longest idle server. Then
--   $$\lim_{\lambda\uparrow\lambda^*}\sum_{u:\,u\cap\mathcal T^*=\emptyset}\mathbb P_{\mathrm{c.o.s.}}(u)=1.$$
--   Here $\mathcal T^*$ also denotes the servers compatible with the job types in $\mathcal T^*$. In other words, these servers are all occupied with probability tending to one.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: the subset 𝒯* that maximizes the capacity ratio is unique, i.e., the vector of critical arrival rates can reach any point on the boundary except for its extreme vertices → IsCriticalSubset, the first sentence of Assumption 3; reason: the clause after i.e. is not equivalent: with N = 3, S_i = {i}, p_1/µ_1 = p_2/µ_2 > p_3/µ_3 the maximizer is not unique and the critical point is not a vertex
--   - reading: u ∩ 𝒯* = ∅ → no idle server lies in serversOf D T; reason: the paper calls the servers compatible with 𝒯* the set 𝒯* as well, p.32
--   - reading: the stationary distribution, whose existence and uniqueness are taken for granted → every family of stationary laws on (0, λ*); reason: the laws exist (the goal proves it) and two servers compatible with no type make the c.o.s. law non-unique, so the universal statement covers the source's law in every case
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Lemma 1, display (42), p.34; notation p.32

import Definitions.Def_BipartiteMatchingHT_Delay_Queue
import Definitions.Def_RedundancyHT_IsCriticalSubset
import Definitions.Def_RedundancyHT_lamStar
import Definitions.Def_RedundancyHT_load

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay Classical
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **Lemma 1, (42)** (arXiv:2005.14566v5, p.34): the servers of `𝒯*` are all busy with probability
tending to one. "u ∩ 𝒯* = ∅" means that no server of `serversOf D T` is idle: the paper calls the
compatible servers "the set 𝒯*" as well (p.32).

**Formalization Note.** The sum is in `ℝ≥0∞`, so no summability is involved. A server compatible with
no type is not in `serversOf D T`, so it makes no difference here. -/
theorem lemma_1 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCriticalSubset D T)
    (π : ℝ → QueueState n m → ℝ≥0∞)
    (hπ : ∀ lam, 0 < lam → lam < lamStar D T → stationary D (load D lam) (π lam)) :
    Tendsto (fun lam => ∑' q, if ∀ j ∈ q.idle, j ∉ serversOf D T then π lam q else 0)
      (𝓝[<] lamStar D T) (𝓝 1) := by sorry

end RedundancyHT
