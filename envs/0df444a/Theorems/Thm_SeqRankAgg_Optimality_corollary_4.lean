-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_corollary_4
-- name    : SeqRankAgg.Optimality.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:34.516229+00:00
-- url     : https://prove2.me/theorems/bb5cb443-fb86-45f3-8375-cb5c483fc03c
-- title:
--   Corollary 4, p. 13 — both ε-greedy GLR policies attain optimal Bayes risk
-- statement:
--   Under A1–A5 and A7, fix $\alpha_h\in(0,1)$ for the stopping threshold and $\delta_0\in(0,1/2)$. Let $p(c)$ be proportional to $|\log c|^{-1/2+\delta_0}$ with any positive constant of proportionality. Using any measurable maximum likelihood selector and any measurable max–min allocation selector, construct the two policies $\pi_i=(A_p,T_i,R)$, $i=1,2$, where $R$ ranks the maximum likelihood estimate at stopping. For each policy,
--
--   $$
--   \lim_{c\downarrow0}\frac{V_c(\rho,\pi_i)}{V_c^*(\rho)}=1.
--   $$
--
--   This says that the concrete sequential procedures attain the unrestricted minimum Bayes risk asymptotically as comparisons become cheap.
--
--   **Formalization Note** The formal conclusion asserts existence of measurable MLE and max–min selectors and of each exact cost-indexed policy family, as well as the limit. This makes the implicit existence claims explicit and rules out vacuous selector or kernel hypotheses. $V_c^*$ ranges over every admissible sequential ranking policy. Exploration is $p(c)=\min\{1,C|\log c|^{-1/2+\delta_0}\}$; clipping changes only costs away from zero. Risks lie in $[0,\infty]$ and limits are from $c>0$.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 13, Corollary 4

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem corollary_4 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ) (hA7 : A7 M ρ)
    (αh : ℝ) (hαh : 0 < αh ∧ αh < 1)
    (δ0 : ℝ) (hδ0 : 0 < δ0 ∧ δ0 < 1 / 2)
    (C : ℝ) (hC : 0 < C) :
    (∃ θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ),
      IsMLESelector M ρ θhat) ∧
    (∃ lamStar : (Fin m → ℝ) → Fin (numPairs m) → ℝ,
      IsMaxMinSelector M ρ lamStar) ∧
    ∀ θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ),
      IsMLESelector M ρ θhat →
    ∀ lamStar : (Fin m → ℝ) → Fin (numPairs m) → ℝ,
      IsMaxMinSelector M ρ lamStar →
    ∀ i : Fin 2, ∃ πfam : ℝ → Policy m,
      IsProposedFamily M ρ θhat lamStar αh δ0 C i πfam ∧
      Tendsto (fun c => bayesRisk M ρ c (πfam c) / optRisk M ρ c)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by sorry

end SeqRankAgg.Optimality
