-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_lemma_D_6
-- name    : TradingPostNSW.Leontief.Supplement.lemma_D_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:38:26.956131+00:00
-- url     : https://prove2.me/theorems/24b77d3c-7e18-4859-9dc1-42a76be567c4
-- title:
--   Lemma D.6, p. 27 (used in the proof of Theorem D.8) — the Leontief fraction function is strictly concave in s_ij and concave in s_i
-- statement:
--   Fix an agent $i$, a good $j$ with $v_{i,j}>0$, and bids $s_{k,\cdot}$ of the other agents forming a *valid* profile: $D_{j'}:=\sum_{k\ne i}s_{k,j'}>0$ for every good $j'$. Consider
--   $$f_j=\frac{1}{v_{i,j}}\cdot\frac{s_{i,j}}{s_{i,j}+D_j}.$$
--   Then $f_j$ is strictly concave as a function of $s_{i,j}\in[0,\infty)$, and concave as a function of agent $i$'s bid vector $(s_{i,1},\dots,s_{i,m})\in\mathbb R^m_{\ge0}$.
--
--   In the Leontief game the utility is the minimum over demanded goods of these fractions, so this lemma is the source of the concavity used to show that best responses are unique.
--
--   Differences from the source:
--   - reading: as a function of (s_{i1}, …, s_{in}) → as a function of agent i's m bids (s_{i,1}, …, s_{i,m}); reason: s_i has one coordinate per good; n is the number of agents, a typo
--   - generalization: a valid strategy profile s_{−i} of TP(∆), ∆ > 0 → any real bids of the other agents with Σ_{k≠i} s_{k,j'} > 0 for every good; reason: the lemma uses only the positivity of these sums; every valid strategy profile qualifies
--   - generalization: concave in s_i on S_i → concave on the whole orthant ℝ^m_{≥0} (strict concavity on [0, ∞) in s_{i,j}); reason: S_i is a convex subset of the orthant, so the claim on S_i follows
--   - encoding: the factor 1/v_{ij} → v_{i,j} > 0 is assumed; reason: 1/v_{i,j} is defined only then; only demanded goods enter the Leontief minimum
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 27, Lemma D.6 and its proof; Definition D.4, p. 27

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem lemma_D_6 {n m : ℕ} (I : Instance n m) (s : Fin n → Fin m → ℝ) (i : Fin n)
    (hvalid : ∀ j, 0 < ∑ k ∈ Finset.univ.erase i, s k j) (j : Fin m) (hv : 0 < I.v i j) :
    StrictConcaveOn ℝ (Set.Ici 0)
        (fun t : ℝ => 1 / I.v i j * (t / (t + ∑ k ∈ Finset.univ.erase i, s k j))) ∧
      ConcaveOn ℝ (orthant m)
        (fun si : Fin m → ℝ =>
          1 / I.v i j * (si j / (si j + ∑ k ∈ Finset.univ.erase i, s k j))) := by sorry

end TradingPostNSW.Leontief.Supplement
