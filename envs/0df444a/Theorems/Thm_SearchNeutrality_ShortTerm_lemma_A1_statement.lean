-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_lemma_A1_statement
-- name    : SearchNeutrality.ShortTerm.lemma_A1_statement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:32.504402+00:00
-- url     : https://prove2.me/theorems/58bab778-f92a-4a97-ace6-d1430a4fb4b6
-- title:
--   Lemma A1 as stated in the Appendix, p. 42 — at the F-prominent equilibrium prices the platform strictly prefers F prominent, and the prices form an equilibrium without neutrality
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, assume Condition 1 and let $\alpha\in[0,1]$. Let $(p_F,p_T)$ be an equilibrium of the pricing game in which $F$ is prominent for all consumers. Then
--
--   1. for each consumer type $k\in\{f,t\}$, the platform's expected profit from one type-$k$ consumer is strictly larger when $F$ is prominent than when $T$ is prominent:
--   $$
--   p_F\,d_F^{k,T\text{ first}}+r\,p_T\,d_T^{k,T\text{ first}}\;<\;p_F\,d_F^{k,F\text{ first}}+r\,p_T\,d_T^{k,F\text{ first}};
--   $$
--   2. there is an optimal ranking rule $\sigma$ such that $(p_F,p_T,\sigma)$ is an equilibrium without search neutrality: no seller gains by a price deviation, even one that makes the platform rank $T$ first for some consumers.
--
--   This is the statement the Appendix attributes to Lemma A1 of the paper's Online Appendix A; it guarantees that the equilibrium computed with $F$ prominent for all is an equilibrium of the full game.
--
--   **Formalization Note** Part 2 is existential in the ranking rule: at deviation prices where the platform is indifferent, the page does not say how ties are broken, so the statement asserts that some optimal tie-breaking supports the equilibrium. The proof of Lemma A1 is in an online appendix that is not part of the source file.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 42, first paragraph (statement of Lemma A1 of Online Appendix A)

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model

namespace SearchNeutrality.ShortTerm

/-- Lemma A1 as the Appendix states it (p. 42): under Condition 1, at the equilibrium prices of the
pricing game with `F` prominent for all consumers, (1) the platform strictly prefers to make `F`
prominent for each consumer type, and (2) together with some optimal ranking rule these prices form
an equilibrium without search neutrality. -/
theorem lemma_A1_statement (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (pF pT : ℝ)
    (heq : IsPriceEquilibrium ρH ρL r α fPrimeAll pF pT) :
    (∀ k : CType, platformTypeProfit ρH ρL r pF pT k .T < platformTypeProfit ρH ρL r pF pT k .F) ∧
    ∃ σ : ℝ → ℝ → Ranking, IsNSEquilibrium ρH ρL r α pF pT σ := by sorry

end SearchNeutrality.ShortTerm
