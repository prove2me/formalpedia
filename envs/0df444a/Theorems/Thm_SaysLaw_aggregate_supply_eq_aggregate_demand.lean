-- Prove2me | Theorems.Thm_SaysLaw_aggregate_supply_eq_aggregate_demand
-- name    : SaysLaw.aggregate_supply_eq_aggregate_demand
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:10.805739+00:00
-- url     : https://prove2.me/theorems/3fbc547b-4a9d-4810-9a31-8444f0f528b9
-- title:
--   Say's identity: aggregate value of demand equals aggregate value of supply
-- statement:
--   Throughout, $\iota$ is a finite set of agents and $G$ a finite set of goods; $p=(p_g)_{g\in G}$ is a real price vector; $s_i=(s_{i,g})_g$ and $d_i=(d_{i,g})_g$ are real vectors giving the quantities agent $i$ brings to market (supplies) and plans to buy (demands); $\langle p,x\rangle=\sum_{g\in G}p_g x_g$ is the market value of a bundle $x$; and $z_g=\sum_{i\in\iota}(d_{i,g}-s_{i,g})$ is the aggregate excess demand for good $g$.
--
--   Suppose every agent obeys Say's budget principle at prices $p$: $\langle p,d_i\rangle=\langle p,s_i\rangle$ for all $i$. Then the total value of planned purchases equals the total value of goods offered for sale:
--
--   $$\sum_{i\in\iota}\langle p,d_i\rangle=\sum_{i\in\iota}\langle p,s_i\rangle .$$
--
--   This is the aggregate form of Say's law in the article: the goods offered for sale are evidence of an equal quantity of demand.
-- source:
--   Wikipedia, "Say's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Say%27s_law

import Mathlib
import Definitions.Def_SaysLaw_Model

namespace SaysLaw

theorem aggregate_supply_eq_aggregate_demand {ι G : Type*} [Fintype ι] [Fintype G]
    (p : G → ℝ) (supply demand : ι → G → ℝ) (hsay : SaysBudget p supply demand) :
    ∑ i, bundleValue p (demand i) = ∑ i, bundleValue p (supply i) := by sorry

end SaysLaw
