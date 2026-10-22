-- Prove2me | Theorems.Thm_PELiquidity_Secondary_lemma_3
-- name    : PELiquidity.Secondary.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:25.600562+00:00
-- url     : https://prove2.me/theorems/1b3765f5-037b-4861-842c-c25a4dbbaf89
-- title:
--   Lemma 3: the primary-market return gap rises with the discount
-- statement:
--   For $D_L\in[1-\delta_H,1-\delta_L]$, let $\bar R^{\min}_{H}(D_L)$ and $\bar R^{\min}_{L}(D_L)$ be the H- and L-LP indifference returns in (C.6) and (C.5). They coincide at $D_L=1-\delta_H$. Their difference rises strictly as the discount increases, so
--   $$
--   D_L>1-\delta_H\quad\Longrightarrow\quad
--   \bar R^{\min}_{H}(D_L)>\bar R^{\min}_{L}(D_L).
--   $$
--   This compares the cost of capital for the two LP types in the presence of secondary trading.
--
--   **Formalization Note** The printed lemma says “higher” on the closed interval, but the paper's calculation (C.7) gives equality at its lower endpoint. The strict claim therefore applies only above that endpoint.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 27, Lemma 3; pp. 49–50, Appendix C.5, (C.7)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Secondary

theorem lemma_3 (P : PELiquidity.Primary.Params) :
    let RminH : ℝ → ℝ := fun D =>
      1 + P.lam * P.δH * D / (1 - D) * PELiquidity.Primary.grossReturn P.lam P.δH
    let RminL : ℝ → ℝ := fun D => 1 / (1 - P.lam * D)
    RminH (1 - P.δH) = RminL (1 - P.δH) ∧
    StrictMonoOn (fun D => RminH D - RminL D)
      (Set.Icc (1 - P.δH) (1 - P.δL)) ∧
    ∀ D ∈ Set.Ioc (1 - P.δH) (1 - P.δL),
      0 < RminH D - RminL D := by sorry

end PELiquidity.Secondary
