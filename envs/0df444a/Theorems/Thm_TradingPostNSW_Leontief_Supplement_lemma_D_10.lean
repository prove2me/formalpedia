-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_lemma_D_10
-- name    : TradingPostNSW.Leontief.Supplement.lemma_D_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:40:23.028663+00:00
-- url     : https://prove2.me/theorems/d700924d-f01d-49ec-8b35-4ffaa9e063ad
-- title:
--   Lemma D.10, p. 28 (used in the proof of Theorem D.12) — the Trading Post utility is concave in own bids, strictly when all goods are bid on by others
-- statement:
--   Let $U:[0,1]^m\to\mathbb R$ be concave, non-decreasing, non-negative and non-satiated (strictly increasing in the product order). Fix agent $i$ and strategies $s_k\in S_k$ of the other agents, and write $D_j=\sum_{k\ne i}s_{k,j}$. Define, for $s_i\in\mathbb R^m_{\ge0}$,
--   $$v_i(s_i,s_{-i})=U\Big(\frac{s_{i,1}}{s_{i,1}+D_1},\dots,\frac{s_{i,m}}{s_{i,m}+D_m}\Big),\qquad \tfrac00:=0.$$
--   Then $s_i\mapsto v_i(s_i,s_{-i})$ is concave, and it is strictly concave if $D_j>0$ for every good $j$.
--
--   Differences from the source:
--   - reading: strictly concave if Σ_{k≠i} s_{ij} > 0 for all j → strictly concave if Σ_{k≠i} s_{k,j} > 0 for all j; reason: the summation index is k; the proof (p. 29) sets D_j = Σ_{k≠i} s_{kj}
--   - generalization: concave in s_i ∈ S_i → concave on the whole orthant ℝ^m_{≥0}; reason: S_i is a convex subset of the orthant
--   - generalization: u_i : ℝ^m_+ → ℝ concave, non-negative, non-decreasing and non-satiated (Appendix D.3) → these conditions only on the box [0,1]^m; reason: every Trading Post allocation lies in the box, so payoffs use only these values; a utility satisfying the conditions on ℝ^m_+ satisfies them on the box, and §2 defines utilities on [0,1]^m
--   - encoding: non-satiated: u(x) > u(y) if x_j ≥ y_j for all j and x_j > y_j for some j → strictly monotone on the box [0,1]^m in the product order; reason: the same condition, stated on the domain of the utilities
--   - encoding: 0/0 is considered as 0 (p. 29) → Lean's division, s/(s + 0) = 1 for s > 0 and 0/0 = 0; reason: the same function
--   - generalization: the ambient market assumptions m > 0, B_k ≥ 1, and enough competition from §2 and Appendix D.3 → these analytic lemmas impose only the displayed utility assumptions and admissibility of opponents; no market-wide competition or budget lower bound is assumed; reason: the concavity conclusions depend on nonnegative opponent bids and the stated positive-sum conditions, not on utility functions of other players or a budget normalization; every source market remains an instance
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 28, Lemma D.10; Claim 2 and proof p. 29; Appendix D.3 assumptions p. 28

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem lemma_D_10 {n m : ℕ} (I : Instance n m) (U : (Fin m → ℝ) → ℝ)
    (hU : IsConcaveUtility U) (hns : StrictMonoOn U (box m))
    (s : Fin n → Fin m → ℝ) (i : Fin n) (hs : ∀ k, k ≠ i → Strategy I k (s k)) :
    ConcaveOn ℝ (orthant m)
        (fun si : Fin m → ℝ =>
          U (fun j => si j / (si j + ∑ k ∈ Finset.univ.erase i, s k j))) ∧
      ((∀ j, 0 < ∑ k ∈ Finset.univ.erase i, s k j) →
        StrictConcaveOn ℝ (orthant m)
          (fun si : Fin m → ℝ =>
            U (fun j => si j / (si j + ∑ k ∈ Finset.univ.erase i, s k j)))) := by sorry

end TradingPostNSW.Leontief.Supplement
