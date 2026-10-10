-- Prove2me | Theorems.Thm_SaysLaw_mill_no_glut_with_excess_money
-- name    : SaysLaw.mill_no_glut_with_excess_money
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:07.727536+00:00
-- url     : https://prove2.me/theorems/b34f520c-a455-4dc2-bcfb-44a70dda04be
-- title:
--   Mill: no excess of all other commodities together with an excess of money
-- statement:
--   Throughout, $\iota$ is a finite set of agents and $G$ a finite set of goods; $p=(p_g)_{g\in G}$ is a real price vector; $s_i=(s_{i,g})_g$ and $d_i=(d_{i,g})_g$ are real vectors giving the quantities agent $i$ brings to market (supplies) and plans to buy (demands); $\langle p,x\rangle=\sum_{g\in G}p_g x_g$ is the market value of a bundle $x$; and $z_g=\sum_{i\in\iota}(d_{i,g}-s_{i,g})$ is the aggregate excess demand for good $g$. Each agent holds money $m_i$ initially and plans to hold $m'_i$.
--
--   Assume there is at least one good, all prices are strictly positive, and every agent satisfies the monetary budget constraint $\langle p,d_i\rangle+m'_i=\langle p,s_i\rangle+m_i$. Then it is impossible that simultaneously
--
--   1. every good is in excess supply ($z_g<0$ for all $g\in G$), and
--   2. money is not in excess demand ($\sum_i(m'_i-m_i)\le 0$).
--
--   This is Mill's rescue of the no-general-glut principle by counting money as one of the commodities.
-- source:
--   Wikipedia, "Say's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Say%27s_law

import Mathlib
import Definitions.Def_SaysLaw_Model

namespace SaysLaw

theorem mill_no_glut_with_excess_money {ι G : Type*} [Fintype ι] [Fintype G] [Nonempty G]
    (p : G → ℝ) (hp : ∀ g, 0 < p g) (supply demand : ι → G → ℝ) (m m' : ι → ℝ)
    (hbudget : MonetaryBudget p supply demand m m') :
    ¬ (GeneralGlut (excessDemand supply demand) ∧ excessMoneyDemand m m' ≤ 0) := by sorry

end SaysLaw
