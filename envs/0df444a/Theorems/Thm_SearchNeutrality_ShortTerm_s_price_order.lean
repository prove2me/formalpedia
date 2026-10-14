-- Prove2me | Theorems.Thm_SearchNeutrality_ShortTerm_s_price_order
-- name    : SearchNeutrality.ShortTerm.s_price_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:31.447325+00:00
-- url     : https://prove2.me/theorems/beb7a2a3-eb10-4beb-b3a0-9f8a5142b550
-- title:
--   Appendix, pp. 44–45, Case A / Case B — with neutrality, p_F ≤ p_T when α ≤ 1/2 and p_T ≤ p_F when α > 1/2
-- statement:
--   Let $1>\rho_H>\rho_L>0$, $r\in[0,1]$, assume Condition 1 and let $\alpha\in[0,1]$. If $(p_F,p_T)$ is an equilibrium with search neutrality ($F$ prominent for type $f$, $T$ prominent for type $t$), then
--   $$
--   \alpha\le\tfrac12\;\Longrightarrow\;p_F\le p_T,\qquad\qquad \alpha>\tfrac12\;\Longrightarrow\;p_T\le p_F .
--   $$
--   The more popular product is the one whose seller, prominent for the larger group, does not undercut. This splits the analysis of the neutral case into the two cases of the Appendix.
--
--   **Formalization Note** Condition 1 enters through $r<1$: at $r=1$ the third-party seller's profit is identically zero and the ordering for $\alpha\le\frac12$ fails.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 44, Case A; p. 45, Case B

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model

namespace SearchNeutrality.ShortTerm

/-- Appendix, pp. 44–45, Case A and Case B: under Condition 1, every equilibrium with search
neutrality has `p_F ≤ p_T` when `α ≤ 1/2` and `p_T ≤ p_F` when `α > 1/2`. -/
theorem s_price_order (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (pF pT : ℝ)
    (heq : IsSEquilibrium ρH ρL r α pF pT) :
    (α ≤ 1 / 2 → pF ≤ pT) ∧ (1 / 2 < α → pT ≤ pF) := by sorry

end SearchNeutrality.ShortTerm
