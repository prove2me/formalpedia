-- Prove2me | Theorems.Thm_TalagrandConc_Chromatic_eq_9_7
-- name    : TalagrandConc.Chromatic.eq_9_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:37.452121+00:00
-- url     : https://prove2.me/theorems/d632b7f1-e03e-48c1-a23b-5ec12341ade1
-- title:
--   Eq. (9.7) — $N=\big(r(r-1)/2\big)^{-1}\sum_{e\in E_0}N(G,e)$
-- statement:
--   Let $G$ be a graph on $V=\{1,\dots,n\}$, let $r\ge2$ be an integer, and for $e=(i,j)\in E_0=\{(i,j);\ i<j\}$ let $N(G,e)$ be the number of independent sets of $G$ of size $r$ containing both $i$ and $j$. Then the total number $N$ of independent sets of $G$ of size $r$ is
--   $$N=\Big(\frac{r(r-1)}{2}\Big)^{-1}\sum_{e\in E_0}N(G,e).$$
--
--   This double-counting identity is used in the proof of Proposition 9.2 to compare the total number of independent $r$-sets with the edge-weighted sum controlled by Theorem 4.1.1.
--
--   **Formalization Note** The page uses (9.7) for $r\ge2$ (for $r\le1$ the factor $r(r-1)/2$ vanishes); the hypothesis $2\le r$ is stated explicitly, and $r(r-1)$ is computed in $\mathbb R$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 165, proof of Proposition 9.2, Eq. (9.7)

import Mathlib
import Definitions.Def_TalagrandConc_Chromatic_Basic

open MeasureTheory
open scoped Classical

namespace TalagrandConc.Chromatic

theorem eq_9_7 {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (hr : 2 ≤ r) :
    ((G.indepSetFinset r).card : ℝ)
      = ((r : ℝ) * ((r : ℝ) - 1) / 2)⁻¹ * ∑ e : EdgeSlot n, (indepCount G r e : ℝ) := by sorry

end TalagrandConc.Chromatic
