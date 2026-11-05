-- Prove2me | Theorems.Thm_ResAllocGaps_hindsight_discussion
-- name    : ResAllocGaps.hindsight_discussion
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:07.971205+00:00
-- url     : https://prove2.me/theorems/6cdc38a5-778d-4b87-af56-cc5d3f3a8423
-- title:
--   Discussion of the Hindsight Optimal (p.ec3) — on $\tilde{\mathcal H}\cap\mathcal C\cap\mathcal P$ hindsight rejects the middle; on $\mathcal H\cap\mathcal C\cap\mathcal P$ it accepts it
-- statement:
--   Fix $\beta>0$, the law $F_\beta$ and $B=\lfloor T/2\rfloor$, with the partition and events of the proof of Theorem 1 (with the corrected $\mathcal P$).
--
--   1. For every $T$, on $\tilde{\mathcal H}\cap\mathcal C\cap\mathcal P$: $N(I_H,1,T)\ge\tfrac12T\ge B$, and every hindsight-optimal selection (a set of at most $B$ times attaining $V^{hs}_1(B,T;\theta)$) rejects all arrivals in $I_L\cup I_{M_p}\cup I_{M_c}$.
--   2. For all sufficiently large $T$, almost surely on $\mathcal H\cap\mathcal C\cap\mathcal P$:
--   $$N(I_H,1,T)+N(I_{M_c},1,T)+N(I_{M_p},1,T)\le\tfrac12T-\tfrac{31}{32}\sqrt T<\lfloor\tfrac12T\rfloor=B,$$
--   and every hindsight-optimal selection accepts all arrivals in $I_H\cup I_{M_p}\cup I_{M_c}$.
--
--   On the two events the benchmark therefore treats the middle windows $I_{M_c}$ in opposite ways, which no online policy can tell apart by time $B$.
--
--   **Formalization Note** Part 2 is almost sure because the abilities lie in the support $[0,\tfrac14]\cup[\tfrac34,1]$ of $F_\beta$; the counting inequality holds on the whole event.
--
--   Differences from the source:
--   - generalization: the events with P₁, P₂ of (EC.9), (EC.10) → the corrected P₁ = {N(I_Mp, 1, B) ≤ √T/64}, P₂ = {N(I_Mp, B+1, T) ≤ √T/64}; reason: the corrected events contain the printed ones, so the statement specializes to the page; the mission uses one corrected P because the printed lower bounds make Lemma EC.4 false
--   - encoding: the hindsight optimal must reject (accept) all arrivals in … → every set S of at most B times attaining hsValue excludes (contains) those times; reason: the paper's hindsight optimal is any maximizer
--   - encoding: conditional on H ∩ C ∩ P, the hindsight optimal must accept all arrivals in I_H ∪ I_Mp ∪ I_Mc → almost surely on H ∩ C ∩ P; reason: the paper's arrivals lie in the support of F_β; off it (a null event) an ability in the gap would be chosen first
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, Appendix EC.1, Proof of Theorem 1, Discussion of the Hindsight Optimal, p.ec3

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy
import Definitions.Def_ResAllocGaps_muBeta
import Definitions.Def_ResAllocGaps_arrivals

open MeasureTheory

namespace ResAllocGaps

/-- **Discussion of the Hindsight Optimal**, Proof of Theorem 1, Besbes, Kanoria & Kumar,
arXiv:2205.09078v2, Appendix EC.1, p.ec3, for `β > 0`, the law `F_β` and `B = ⌊T/2⌋`:
1. on `H̃ ∩ C ∩ P`, `N(I_H, 1, T) ≥ T/2 ≥ B`, and every hindsight-optimal selection rejects all
   arrivals in `I_L ∪ I_{Mp} ∪ I_{Mc}`;
2. for sufficiently large `T`, on `H ∩ C ∩ P`,
   `N(I_H, 1, T) + N(I_{Mc}, 1, T) + N(I_{Mp}, 1, T) ≤ T/2 − (31/32)√T < ⌊T/2⌋ = B`, and every
   hindsight-optimal selection accepts all arrivals in `I_H ∪ I_{Mp} ∪ I_{Mc}`.

**Formalization Note.** `P` is the corrected event (`eventP1`, `eventP2`). A hindsight-optimal
selection is a set `S` of at most `B` times attaining `hsValue`. Part 2 holds almost surely (the
abilities lie in the support `[0, 1/4] ∪ [3/4, 1]` of `F_β`); its counting inequality holds on the
whole event. -/
theorem hindsight_discussion (β : ℝ) (hβ : 0 < β) :
    (∀ T : ℕ, ∀ ω ∈ eventHt β T ∩ eventC β T ∩ eventP β T,
      (halfBudget T : ℝ) ≤ (T : ℝ) / 2 ∧ (T : ℝ) / 2 ≤ (arrivals (IH β T) 1 T ω : ℝ) ∧
      ∀ S : Finset (Fin T), S.card ≤ halfBudget T →
        ∑ t ∈ S, (ω t).1 = hsValue T (halfBudget T) (abilities ω) →
        ∀ t ∈ S, (ω t).1 ∉ IL β T ∪ IMp β T ∪ IMc β T) ∧
    ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ᵐ ω ∂(sampleLaw (muBeta β) T),
      ω ∈ eventH β T ∩ eventC β T ∩ eventP β T →
        ((arrivals (IH β T) 1 T ω : ℝ) + (arrivals (IMc β T) 1 T ω : ℝ) +
            (arrivals (IMp β T) 1 T ω : ℝ) ≤ (T : ℝ) / 2 - 31 / 32 * √(T : ℝ) ∧
          (T : ℝ) / 2 - 31 / 32 * √(T : ℝ) < (halfBudget T : ℝ)) ∧
        ∀ S : Finset (Fin T), S.card ≤ halfBudget T →
          ∑ t ∈ S, (ω t).1 = hsValue T (halfBudget T) (abilities ω) →
          ∀ t : Fin T, (ω t).1 ∈ IH β T ∪ IMp β T ∪ IMc β T → t ∈ S := by sorry

end ResAllocGaps
