-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_lemma_10
-- name    : SeqRankAgg.Optimality.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:32.805866+00:00
-- url     : https://prove2.me/theorems/40a5e854-bd33-4cfb-a3f4-5f7d3d9ba776
-- title:
--   Lemma 10, p. 25 — the GLR stopping times exceed τ = Ω(|log c|³) with probability at most c²
-- statement:
--   Assume A1–A5 and A7, fix $\alpha_h\in(0,1)$ in the threshold $h(c)=|\log c|(1+|\log c|^{-\alpha_h})$, and let $(\mathcal A_c)_{c>0}$ be a cost-indexed family of adaptive pair-selection rules satisfying A6. For either stopping rule $T_i$ ($i=1,2$) of (3.1)–(3.2) the following holds: for every constant $C>0$ there is $c_0>0$ such that for all $0<c<c_0$, every integer $\tau\ge C|\log c|^3$ and every true parameter $\theta\in W$,
--
--   $$
--   \mathbb P_\theta\big(T_i\ge\tau\big)\le c^2,
--   $$
--
--   where $\mathbb P_\theta$ is the law of the comparison process under $\theta$ and the selection rule $\mathcal A_c$.
--
--   The lemma rules out very long runs of the generalized likelihood ratio stopping rules, which controls the contribution of the tail of $T_i$ to the expected Kendall loss and the expected sample size.
--
--   **Formalization Note** "$\tau=\Omega(|\log c|^3)$" is read as $\tau\ge C|\log c|^3$ for an arbitrary fixed $C>0$, with the threshold $c_0$ allowed to depend on $C$, on the model and on the selection family (through A6's exponent) but uniform over $\theta\in W$ and $\tau$, matching the paper's convention that $O(\cdot)$ is uniform in $\theta$.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 25, Lemma 10; proof pp. 40–42, Appendix E

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem lemma_10 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ) (hA7 : A7 M ρ)
    (αh : ℝ) (hαh : 0 < αh ∧ αh < 1) (i : Fin 2)
    (Afam : ℝ → BanditAlgorithm.BanditPolicy (numPairs m)) (hA6 : A6 M ρ Afam) :
    ∀ C : ℝ, 0 < C →
      ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ τ : ℕ, C * |Real.log c| ^ 3 ≤ (τ : ℝ) → ∀ θ ∈ W ρ,
          BanditAlgorithm.banditTrajMeasure (bandit M θ) (Afam c)
            {ω | (τ : ℕ∞) ≤ (if i = 0 then T1 M ρ αh c else T2 M ρ αh c) ω} ≤
            ENNReal.ofReal (c ^ 2) := by sorry

end SeqRankAgg.Optimality
