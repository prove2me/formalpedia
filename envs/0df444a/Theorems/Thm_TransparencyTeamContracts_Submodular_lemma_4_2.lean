-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_lemma_4_2
-- name    : TransparencyTeamContracts.Submodular.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:55.378552+00:00
-- url     : https://prove2.me/theorems/1c57b036-96d4-4994-8116-166530cc019e
-- title:
--   Lemma 4.2 — Potential Lemma
-- statement:
--   Let $f:2^{[n]}\to[0,1]$ be monotone submodular and $c_i\ge0$. Let $S\subseteq[n]$ be any team, possibly empty, with $c_i>0$ for each $i\in S$. Choose arbitrary benchmarks $\kappa_i>0$ on $S$ with $\sum_{i\in S}\kappa_i\le1$, and define $d_i=c_i/\kappa_i$ and $p_i=f(S)-f(S\setminus\{i\})$. Then
--   $$V(f,c)\ge\left(1-\sum_{i\in S}\kappa_i\right)\left(f(S)-\frac14\sum_{i\in S}d_i\right)+\sum_{i\in S}\kappa_i(p_i-d_i).$$
--   Benchmark shares need not incentivize $S$ under $f$. Strictly positive costs are required only on $S$. The conclusion bounds the actual stateless optimum, independently of any pruning algorithm.
--
--   Differences from the source:
--   - encoding: finite agents and states, real probabilities and contracts, optimal utilities → Fin indices, a simplex prior, and suprema of operational contract and public-scheme payoffs; reason: finite relabeling preserves all instances; admissible payoff sets are nonempty and bounded, and suprema give the same optimal values without asserting attainment
--   - encoding: monotone submodularity with marginals tested for every agent → monotone IsSuccess plus the published diminishing-returns predicate for agents outside the larger set; reason: the omitted membership cases follow from monotonicity, so the function class is identical
--   - encoding: benchmark shares indexed by S and the associated d_i and p_i → a share function on all agents, read only on S, with quotients and marginals substituted into the formula; reason: every family on S extends to all agents, unused values have no effect, and strict positivity on S protects every quotient
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma 4.2, equation (3), printed p.10 (PDF p.12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1292.pdf; PDF SHA-256 0aa8b61daf25346bcfca67a178c55762d05abe3f79b2b66a6d2ad6dfed9b3321

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Game

open Finset

namespace TransparencyTeamContracts.Submodular

/-- Lemma 4.2 (Potential Lemma), printed p.10 (PDF 12), equation (3).
The benchmark shares need not incentivize S. The team may be empty. -/
theorem lemma_4_2 {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsSuccess f) (hsub : SubsamplingSM.Offline.IsSubmodular f)
    (hc : ∀ i, 0 ≤ c i) (S : Finset (Fin n)) (κ : Fin n → ℝ)
    (hcost : ∀ i ∈ S, 0 < c i) (hκ : ∀ i ∈ S, 0 < κ i)
    (hsum : ∑ i ∈ S, κ i ≤ 1) :
    (1 - ∑ i ∈ S, κ i) * (f S - (1 / 4 : ℝ) * ∑ i ∈ S, c i / κ i) +
      (∑ i ∈ S, κ i * (teamMarginal f S i - c i / κ i)) ≤ V f c := by sorry

end TransparencyTeamContracts.Submodular
