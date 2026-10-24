-- Prove2me | Theorems.Thm_RandomPromo_TwoPoint_lemma_5
-- name    : RandomPromo.TwoPoint.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:34.394204+00:00
-- url     : https://prove2.me/theorems/40f1a1e4-9f9b-458d-b3af-1a2b685746b7
-- title:
--   Lemma 5 (as proved, Online Supplement p. 8) — moving all mass above vL to vH keeps a solution of (3) feasible and does not lower its profit
-- statement:
--   Under the standing assumptions $0<c_L<v_L<v_H$, $0<c_H<v_H$, $0<\alpha<1$, let $F$ be a finitely supported price distribution on $\mathbb R$ feasible for problem (3), i.e. $\mathbb E_F[(v_L-P)^+]>c_L$ and $\mathbb E_F[(v_H-P)^+]\le c_H$. Define $G$ to agree with $F$ at every price $p\le v_L$, to put no mass on prices in $(v_L,\infty)\setminus\{v_H\}$, and to put mass $1-F(v_L)$ at $v_H$. Then $G$ is a price distribution, $G$ is feasible for (3), and
--   $$\alpha\,\mathbb E_F[P\mid P\le v_L]+(1-\alpha)F(v_H)\mathbb E_F[P\mid P\le v_H]\le \alpha\,\mathbb E_G[P\mid P\le v_L]+(1-\alpha)G(v_H)\mathbb E_G[P\mid P\le v_H].$$
--
--   The printed Lemma 5 (p. 14) reads: "Let $R_P$ be the support of any optimal price distribution of problem (3). If there exists $p\in R_P$ such that $p>v_L$, then $p=v_H$." This theorem is the dominance argument its proof establishes. It reduces the search for upper bounds on (3) to laws whose only price above $v_L$ is $v_H$.
--
--   **Formalization Note** Problem (3) has a strict constraint and no optimal solution (every feasible law earns strictly less than a value attained in the limit by other feasible laws), so the printed lemma, which quantifies over optimal solutions, is vacuous. The statement posed here is the content of its proof on Online Supplement p. 8. $G$ is pinned by its masses: equal to $F$ on $(-\infty,v_L]$, zero on $(v_L,\infty)$ except at $v_H$, and $1-F(v_L)$ at $v_H$.
-- source:
--   Chen, Hu, Wu, Intertemporal Price Discrimination via Randomized Promotions, SSRN preprint 3223844 (revision of 2022-11-16), p. 14, Lemma 5; Online Supplement p. 8, proof of Lemma 5

import Mathlib
import Definitions.Def_RandomPromo_TwoPoint_Setting

namespace RandomPromo.TwoPoint
theorem lemma_5 (M : Params) (hM : M.Standing) (w : ℝ →₀ ℝ) (hw : IsPriceDist w)
    (hF : M.Feas w) :
    ∃ g : ℝ →₀ ℝ, IsPriceDist g ∧ M.Feas g ∧
      (∀ p, p ≤ M.vL → g p = w p) ∧
      (∀ p, M.vL < p → p ≠ M.vH → g p = 0) ∧
      g M.vH = 1 - cdf w M.vL ∧
      M.obj3 w ≤ M.obj3 g := by sorry
end RandomPromo.TwoPoint
