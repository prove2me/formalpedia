-- Prove2me | Theorems.Thm_SaysLaw_monetary_walras_law
-- name    : SaysLaw.monetary_walras_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:27.641674+00:00
-- url     : https://prove2.me/theorems/9e0dd176-dc4c-47cc-b480-b4c398209800
-- title:
--   Monetary budget identity: value of excess demand for goods plus excess demand for money is zero
-- statement:
--   Throughout, $\iota$ is a finite set of agents and $G$ a finite set of goods; $p=(p_g)_{g\in G}$ is a real price vector; $s_i=(s_{i,g})_g$ and $d_i=(d_{i,g})_g$ are real vectors giving the quantities agent $i$ brings to market (supplies) and plans to buy (demands); $\langle p,x\rangle=\sum_{g\in G}p_g x_g$ is the market value of a bundle $x$; and $z_g=\sum_{i\in\iota}(d_{i,g}-s_{i,g})$ is the aggregate excess demand for good $g$. Each agent also holds money: $m_i$ initially and $m'_i$ as planned.
--
--   If every agent satisfies the monetary budget constraint $\langle p,d_i\rangle+m'_i=\langle p,s_i\rangle+m_i$, then
--
--   $$\langle p,z\rangle+\sum_{i\in\iota}(m'_i-m_i)=0 .$$
--
--   Thus the value of the aggregate excess demand for goods is exactly the negative of the aggregate excess demand for money: a deficiency of demand for goods in value terms is the same thing as an excess demand for money (hoarding), as in J. S. Mill's account of a general glut.
-- source:
--   Wikipedia, "Say's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Say%27s_law

import Mathlib
import Definitions.Def_SaysLaw_Model

namespace SaysLaw

theorem monetary_walras_law {ι G : Type*} [Fintype ι] [Fintype G]
    (p : G → ℝ) (supply demand : ι → G → ℝ) (m m' : ι → ℝ)
    (hbudget : MonetaryBudget p supply demand m m') :
    bundleValue p (excessDemand supply demand) + excessMoneyDemand m m' = 0 := by sorry

end SaysLaw
