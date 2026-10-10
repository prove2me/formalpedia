-- Prove2me | Theorems.Thm_SaysLaw_no_general_glut
-- name    : SaysLaw.no_general_glut
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:13.451526+00:00
-- url     : https://prove2.me/theorems/78c93ed3-bf84-40b7-8344-2de2ffbdcf8a
-- title:
--   Say's law: there can never be a general glut
-- statement:
--   Throughout, $\iota$ is a finite set of agents and $G$ a finite set of goods; $p=(p_g)_{g\in G}$ is a real price vector; $s_i=(s_{i,g})_g$ and $d_i=(d_{i,g})_g$ are real vectors giving the quantities agent $i$ brings to market (supplies) and plans to buy (demands); $\langle p,x\rangle=\sum_{g\in G}p_g x_g$ is the market value of a bundle $x$; and $z_g=\sum_{i\in\iota}(d_{i,g}-s_{i,g})$ is the aggregate excess demand for good $g$.
--
--   Assume there is at least one good, all prices are strictly positive ($p_g>0$), and every agent obeys Say's budget principle — products are paid for with products, so each agent spends the full value of what he sells on other products: $\langle p,d_i\rangle=\langle p,s_i\rangle$. Then there is no general glut:
--
--   $$\neg\big(\forall g\in G,\ z_g<0\big),$$
--
--   that is, some good $g$ has $z_g\ge 0$.
--
--   This is the modern formulation of Say's law quoted in the article: "there can never be a general glut".
-- source:
--   Wikipedia, "Say's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Say%27s_law

import Mathlib
import Definitions.Def_SaysLaw_Model

namespace SaysLaw

theorem no_general_glut {ι G : Type*} [Fintype ι] [Fintype G] [Nonempty G]
    (p : G → ℝ) (hp : ∀ g, 0 < p g) (supply demand : ι → G → ℝ)
    (hsay : SaysBudget p supply demand) :
    ¬ GeneralGlut (excessDemand supply demand) := by sorry

end SaysLaw
