-- Prove2me | Theorems.Thm_SaysLaw_glut_balanced_by_shortage
-- name    : SaysLaw.glut_balanced_by_shortage
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:41.512965+00:00
-- url     : https://prove2.me/theorems/36bb046c-ec01-4c58-9e22-2d8b29296e92
-- title:
--   A glut of one good is balanced by a shortage of another
-- statement:
--   Throughout, $\iota$ is a finite set of agents and $G$ a finite set of goods; $p=(p_g)_{g\in G}$ is a real price vector; $s_i=(s_{i,g})_g$ and $d_i=(d_{i,g})_g$ are real vectors giving the quantities agent $i$ brings to market (supplies) and plans to buy (demands); $\langle p,x\rangle=\sum_{g\in G}p_g x_g$ is the market value of a bundle $x$; and $z_g=\sum_{i\in\iota}(d_{i,g}-s_{i,g})$ is the aggregate excess demand for good $g$.
--
--   Assume all prices are strictly positive, $p_g>0$ for every $g$, and every agent obeys Say's budget principle $\langle p,d_i\rangle=\langle p,s_i\rangle$. If some good $g_0$ is in excess supply, $z_{g_0}<0$, then some *other* good is in excess demand:
--
--   $$\exists\, g\neq g_0\ \text{ with }\ z_g>0 .$$
--
--   This is Say's claim that "the superabundance of goods of one description arises from the deficiency of goods of another description".
-- source:
--   Wikipedia, "Say's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Say%27s_law

import Mathlib
import Definitions.Def_SaysLaw_Model

namespace SaysLaw

theorem glut_balanced_by_shortage {ι G : Type*} [Fintype ι] [Fintype G]
    (p : G → ℝ) (hp : ∀ g, 0 < p g) (supply demand : ι → G → ℝ)
    (hsay : SaysBudget p supply demand) (g₀ : G)
    (hglut : excessDemand supply demand g₀ < 0) :
    ∃ g, g ≠ g₀ ∧ 0 < excessDemand supply demand g := by sorry

end SaysLaw
