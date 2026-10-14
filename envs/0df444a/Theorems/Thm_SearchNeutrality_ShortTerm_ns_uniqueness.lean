-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_ns_uniqueness
-- name    : SearchNeutrality.ShortTerm.ns_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:32.867985+00:00
-- url     : https://prove2.me/theorems/2d93ce51-e6cf-40a9-b5f5-e875de6fe090
-- title:
--   p. 16 — without neutrality the equilibrium prices are unique for every α ∈ [0,1] under Condition 1
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, assume Condition 1 and let $\alpha\in[0,1]$. If $(p_F,p_T,\sigma)$ and $(p_F',p_T',\sigma')$ are two equilibria without search neutrality (possibly with different optimal ranking rules), then
--   $$
--   p_F=p_F',\qquad p_T=p_T'.
--   $$
--   Together with Lemma A1 this identifies every equilibrium without neutrality with the equilibrium of the game in which $F$ is prominent for all consumers, which is what the comparison of consumer surplus needs.
--
--   **Formalization Note** The page asserts uniqueness ("a unique pure-strategy equilibrium exists for all $\alpha\in[0,1]$ under Condition 1"). The Appendix proves uniqueness inside the game with $F$ prominent for all and refers the rest to Lemma A1 of an online appendix that is not part of the source file.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), p. 16, sentence before Proposition 1; Appendix, p. 43 (end of case (B))

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model

namespace SearchNeutrality.ShortTerm

/-- p. 16: under Condition 1, the equilibrium without search neutrality is unique for every
`α ∈ [0,1]`: any two equilibria (with possibly different optimal ranking rules) have the same
prices. -/
theorem ns_uniqueness (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (pF pT : ℝ) (σ : ℝ → ℝ → Ranking) (pF' pT' : ℝ) (σ' : ℝ → ℝ → Ranking)
    (h : IsNSEquilibrium ρH ρL r α pF pT σ) (h' : IsNSEquilibrium ρH ρL r α pF' pT' σ') :
    pF = pF' ∧ pT = pT' := by sorry

end SearchNeutrality.ShortTerm
