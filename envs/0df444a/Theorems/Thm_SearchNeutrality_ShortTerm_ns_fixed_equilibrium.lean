-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_ns_fixed_equilibrium
-- name    : SearchNeutrality.ShortTerm.ns_fixed_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:39:34.308885+00:00
-- url     : https://prove2.me/theorems/9514528b-1598-4742-8df3-eda75bd402fa
-- title:
--   Appendix, pp. 42–43, cases (A)–(B) — the equilibrium with F prominent for all: the interior closed form when the (A2) bracket is negative, (1, 1/2) otherwise
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, assume Condition 1 ($r\le 0.64\rho_L/\rho_H$, $\rho_L\le 0.975$) and let $\alpha\in[0,1]$. Write
--   $$
--   B(\alpha)=\alpha(\rho_H-\rho_L)(2+(3-r)\rho_H\rho_L)+\rho_L(2-(3-r)\rho_H^2).
--   $$
--   In the pricing game where the platform makes $F$ prominent for all consumers, $(p_F,p_T)$ is a Nash equilibrium on $[0,1]^2$ if and only if
--
--   1. $B(\alpha)<0$ and $(p_F,p_T)=(p_F^{NS},p_T^{NS})$, the interior closed forms of the Appendix (p. 43); or
--   2. $B(\alpha)\ge0$ and $(p_F,p_T)=(1,\tfrac12)$.
--
--   In particular the equilibrium exists and is unique for every $\alpha$. This is the computation behind Proposition 1: the paper's Lemma A1 then shows that these prices remain an equilibrium when the platform also chooses the ranking.
--
--   **Formalization Note** The page writes the condition of case (A2) with the factor $2+3\rho_H\rho_L$, a slip for $2+(3-r)\rho_H\rho_L$ (the factor of $\alpha_{NS,1}$ and of case (B)). The page also restates the condition as $\alpha<\alpha_1^{NS}$; that restatement fails at $\alpha=1$ when $\rho_L>\sqrt{2/(3-r)}$ (there $\alpha_1^{NS}=1$ but $B(1)<0$ and the equilibrium is interior), so the statement uses the page's primary condition $B(\alpha)<0$.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 42, case (A) and the definition of α_{NS,1}; p. 43, case (B) and display "Equilibrium prices without search neutrality"

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model
import Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms

namespace SearchNeutrality.ShortTerm

/-- Appendix, pp. 42–43, cases (A) and (B) and the display "Equilibrium prices without search
neutrality": under Condition 1, with `F` prominent for all consumers, `(p_F, p_T)` is an
equilibrium of the pricing game iff it is the interior closed form (when the bracket of (A2) is
negative) or `(1, 1/2)` (when it is nonnegative). -/
theorem ns_fixed_equilibrium (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (pF pT : ℝ) :
    IsPriceEquilibrium ρH ρL r α fPrimeAll pF pT ↔
      ((nsBracket ρH ρL r α < 0 ∧ pF = pFNS ρH ρL r α ∧ pT = pTNS ρH ρL r α) ∨
       (0 ≤ nsBracket ρH ρL r α ∧ pF = 1 ∧ pT = 1 / 2)) := by sorry

end SearchNeutrality.ShortTerm
