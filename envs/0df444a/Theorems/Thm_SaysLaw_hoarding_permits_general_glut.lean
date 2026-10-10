-- Prove2me | Theorems.Thm_SaysLaw_hoarding_permits_general_glut
-- name    : SaysLaw.hoarding_permits_general_glut
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:42.46247+00:00
-- url     : https://prove2.me/theorems/9c0c36d1-6969-4f16-9193-11a86d3e257a
-- title:
--   With money hoarding, a general glut is consistent with every agent's budget
-- statement:
--   Throughout, $\iota$ is a finite set of agents and $G$ a finite set of goods; $p=(p_g)_{g\in G}$ is a real price vector; $s_i=(s_{i,g})_g$ and $d_i=(d_{i,g})_g$ are real vectors giving the quantities agent $i$ brings to market (supplies) and plans to buy (demands); $\langle p,x\rangle=\sum_{g\in G}p_g x_g$ is the market value of a bundle $x$; and $z_g=\sum_{i\in\iota}(d_{i,g}-s_{i,g})$ is the aggregate excess demand for good $g$. Each agent holds money $m_i$ initially.
--
--   Assume there is at least one agent. For any prices $p$, any supplies $s$ and any initial money balances $m$, there exist demands $d$ and planned money balances $m'$ such that every agent satisfies the monetary budget constraint $\langle p,d_i\rangle+m'_i=\langle p,s_i\rangle+m_i$ and yet
--
--   $$z_g<0\quad\text{for every good }g\in G,$$
--
--   i.e. there is a general glut. Once agents may hold on to the proceeds of sales as money instead of spending them, the budget constraints alone no longer rule out a general glut, which is the Keynesian and Marxian objection to Say's law.
-- source:
--   Wikipedia, "Say's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Say%27s_law

import Mathlib
import Definitions.Def_SaysLaw_Model

namespace SaysLaw

theorem hoarding_permits_general_glut {ι G : Type*} [Fintype ι] [Nonempty ι] [Fintype G]
    (p : G → ℝ) (supply : ι → G → ℝ) (m : ι → ℝ) :
    ∃ (demand : ι → G → ℝ) (m' : ι → ℝ),
      MonetaryBudget p supply demand m m' ∧ GeneralGlut (excessDemand supply demand) := by sorry

end SaysLaw
