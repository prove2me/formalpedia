-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_ap_satisfies_a6_a8
-- name    : SeqRankAgg.Optimality.ap_satisfies_a6_a8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:37.549285+00:00
-- url     : https://prove2.me/theorems/6e3a2d2d-db52-47f6-abde-4f06302c48ca
-- title:
--   §3.2, p. 13 — ε-greedy selection satisfies A6 and A8
-- statement:
--   Let $p(c)$ be an exploration probability for the paper’s ε-greedy pair-selection family $A_p$. If $p(c)\to0$ and, for some $\delta_0>0$, eventually $p(c)\ge|\log c|^{-1/2+\delta_0}$ as $c\downarrow0$, then
--
--   $$
--   A_p\text{ satisfies A6 and A8.}
--   $$
--
--   The claim connects the explicit uniform-exploration mixture in Algorithm 1 with the two conditions used by Theorems 2 and 3.
--
--   **Formalization Note** A6 says *there exists* a positive exponent; it does not require the same $\delta_0$ as the lower bound on $p$. This distinction absorbs the factor $2/[K(K-1)]$ in each pair’s uniform exploration probability. The first comparison is uniformly sampled.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 13, §3.2, unnumbered claim beginning “It is straightforward to see”

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem ap_satisfies_a6_a8 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ) (hA7 : A7 M ρ)
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ))
    (hθhat : IsMLESelector M ρ θhat)
    (lamStar : (Fin m → ℝ) → Fin (numPairs m) → ℝ)
    (hLam : IsMaxMinSelector M ρ lamStar)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (p : ℝ → ℝ)
    (hpLower : ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |Real.log c| ^ (-(1 / 2 : ℝ) + δ0) ≤ p c)
    (hpZero : Tendsto p (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (Afam : ℝ → BanditAlgorithm.BanditPolicy (numPairs m))
    (hgreedy : IsEpsGreedyFamily θhat lamStar p Afam) :
    A6 M ρ Afam ∧ A8 θhat lamStar Afam := by sorry

end SeqRankAgg.Optimality
