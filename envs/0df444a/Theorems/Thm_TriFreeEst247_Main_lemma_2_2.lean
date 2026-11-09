-- Prove2me | Theorems.Thm_TriFreeEst247_Main_lemma_2_2
-- name    : TriFreeEst247.Main.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:07:21.473328+00:00
-- url     : https://prove2.me/theorems/eafbe360-3227-4fc0-8f0e-69e058a47a10
-- title:
--   Lemma 2.2: estimating the penalized optimum
-- statement:
--   There are absolute $C>0$ and $d\in\mathbb N$ such that for every real $\lambda\ge0$ and $0<\zeta<1$, one randomized adjacency-query family, chosen before the input graph, has a uniform worst-case bound
--
--   $$q\le C(1+\lambda)^d\zeta^{-d}.$$
--
--   For every graph $G$ of any order $n\ge1$, its real output $\widehat S$ satisfies
--
--   $$\Pr[|\widehat S-\mathrm{OPT}_\lambda(G)|\le\zeta]\ge5/6.$$
--
--   The algorithm may depend on $\lambda,\zeta,n$ but cannot depend on $G$. This includes the small graph orders as in the source.
--
--   Differences from the source:
--   - encoding: finite graphs and their vertex sets → simple graphs on Fin n, with unordered edges and triangles; reason: relabeling preserves every source instance and all normalized quantities
--   - reading: poly(1+λ, 1/ζ) → C (1+λ)ᵈ ζ⁻ᵈ with C,d before λ,ζ,n,G; reason: the polynomial and O constants are absolute and quantified before every varying parameter
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.7, Lemma 2.2

import Mathlib
import Definitions.Def_TriFreeEst247_Main_Score

open scoped ENNReal

namespace TriFreeEst247.Main

theorem lemma_2_2 :
    ∃ C : ℝ, ∃ d : ℕ, 0 < C ∧ ∀ lam ζ : ℝ, 0 ≤ lam → 0 < ζ → ζ < 1 →
      ∃ q : ℕ, (q : ℝ) ≤ C * (1 + lam)^d * ζ⁻¹^d ∧
      ∃ alg : GraphAlgorithm ℝ, hasQueryBound alg q ∧
        ∀ n, 1 ≤ n → ∀ G : Graph n,
          (5 / 6 : ℝ≥0∞) ≤ outputProb (alg n) (graphOracle G) (fun z => |z - scoreOpt G lam| ≤ ζ)
    := by sorry

end TriFreeEst247.Main
