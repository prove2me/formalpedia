-- Prove2me | Theorems.Thm_RankingCertGap_lemma_4
-- name    : RankingCertGap.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:29.602056+00:00
-- url     : https://prove2.me/theorems/b8451bb3-a9fa-474c-99a7-b328a2081205
-- title:
--   Lemma 4, p.18 — independent or mutually exclusive safety events
-- statement:
--   Let $G$ have online degree at most two, and fix an arrival prefix. There is a family of rooted order states $(W_i,\prec_i;i)$, one representing each positive offline node, with the following property. For any distinct positive nodes $i_1,i_2$, exactly one of the following holds.
--
--   1. The witness sets are disjoint, the safety events are independent, and if $\Pr[\mathcal E_{i_k}\mid Y_{i_k}=y]=a_ky^{p_k}$ on $[0,1]$ then
--
--   $$
--   \Pr[\mathcal E_{i_1}\cap\mathcal E_{i_2}\mid Y_{i_1}=x,Y_{i_2}=y]=a_1a_2x^{p_1}y^{p_2}\qquad(x,y\in[0,1]).
--   $$
--
--   2. The safety events are mutually exclusive: $\Pr[\mathcal E_{i_1}\cap\mathcal E_{i_2}]=0$.
--
--   This dichotomy is what reduces every degree-two edge score to independent roots with monomial profiles.
--
--   Differences from the source:
--   - reading: rooted order states "from the recursive construction above" → there exists a family of rooted order states representing all positive nodes for which the dichotomy holds for every pair; reason: the construction is a proof device and is not defined inside the statement; this is the shape of Lemma 35, and it asserts the family and the dichotomy simultaneously for all pairs
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Lemma 4, p.18; Lemma 35, p.53; App. E.1.3, pp.55–56

import Mathlib
import Definitions.Def_RankingCertGap_RankingRun
import Definitions.Def_RankingCertGap_Score
import Definitions.Def_RankingCertGap_OrderState

open MeasureTheory

namespace RankingCertGap

/-- **Lemma 4 (Independent or mutually exclusive safety events).** Xu, arXiv:2610.17545 (held file
sha256 75896dd9…), Lemma 4, p.18: for distinct positive offline nodes `i₁, i₂` after the same prefix,
with rooted order states from the recursive construction, exactly one of two cases holds. (1) The
witness sets are disjoint; the safety events are then independent, and with monomial parameters
`(a₁, p₁)`, `(a₂, p₂)` one has `Pr[E_{i₁} ∩ E_{i₂} | Y_{i₁} = x, Y_{i₂} = y] = a₁a₂x^{p₁}y^{p₂}`
(eq. (39)). (2) The safety events are mutually exclusive: `Pr[E_{i₁} ∩ E_{i₂}] = 0` (eq. (40)).

**Formalization Note.** The order states "from the recursive construction" are a choice of one
state per node, made simultaneously. So the statement is existential: there is a family of rooted
order states representing all positive nodes after the prefix such that every distinct positive
pair satisfies the dichotomy (the shape of Lemma 35, p.53). "Exactly one" is `Xor`. The monomial
parameters are those of Corollary 1: any `(a, p)` representing the conditional safety probability
on `[0, 1]`. -/
theorem lemma_4 {m n : ℕ} (G : Inst m n) (hG : G.IsOnlineDegLE 2) (t : ℕ) (ht : t ≤ n) :
    ∃ (W : Fin m → Finset (Fin m)) (r : Fin m → Fin m → Fin m → Prop),
      (∀ i, 0 < (rankMeasure m).real (G.safeEvent t i) →
        IsRootedOrderState (W i) (r i) i ∧
          ∀ Y : Fin m → ℝ, DistinctRanks Y → (G.safeAfter Y t i ↔ orderEvent (W i) (r i) Y)) ∧
      ∀ i₁ i₂ : Fin m, i₁ ≠ i₂ →
        0 < (rankMeasure m).real (G.safeEvent t i₁) →
        0 < (rankMeasure m).real (G.safeEvent t i₂) →
        Xor
          (Disjoint (W i₁) (W i₂) ∧
            (rankMeasure m).real (G.safeEvent t i₁ ∩ G.safeEvent t i₂) =
              (rankMeasure m).real (G.safeEvent t i₁) * (rankMeasure m).real (G.safeEvent t i₂) ∧
            ∀ (a₁ a₂ : ℝ) (p₁ p₂ : ℕ),
              (∀ y ∈ Set.Icc (0 : ℝ) 1, G.condSafe t i₁ y = a₁ * y ^ p₁) →
              (∀ y ∈ Set.Icc (0 : ℝ) 1, G.condSafe t i₂ y = a₂ * y ^ p₂) →
              ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
                G.condSafePair t i₁ i₂ x y = a₁ * a₂ * x ^ p₁ * y ^ p₂)
          ((rankMeasure m).real (G.safeEvent t i₁ ∩ G.safeEvent t i₂) = 0) := by sorry

end RankingCertGap
