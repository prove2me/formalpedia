-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_dual_convex_and_attains_minimum
-- name    : PandoraBO.Private20261023.dual_convex_and_attains_minimum
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:15.284991+00:00
-- url     : https://prove2.me/theorems/e4a6e3f4-8d17-43d7-9115-4c7675c226b6
-- title:
--   Lemma 6 — convexity and attainment of the dual minimum
-- statement:
--   Fix $B$ and suppose some box has cost strictly below $B$. Define
--
--   $$A_B(\lambda)=\sup_\pi\{R(\pi)-\lambda C(\pi)\}+\lambda B.$$
--
--   Then $A_B$ is convex on $[0,\infty)$ and attains its minimum there. The supremum ranges over the full measurable adaptive randomized policy class. No positivity of the minimizing multiplier is asserted here.
-- source:
--   Xie, Astudillo, Frazier, Scully and Terenin, Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index, NeurIPS 2024; arXiv:2406.20062v3 (16 January 2025), https://arxiv.org/pdf/2406.20062v3, Appendix B.5, p. 20, Lemma 6 and definition of the Lagrangian envelope in equations (35)–(39). Mission source version: the author-revised manuscript reviewed on 23 October 2026, intended for arXiv v4; public posting is pending. References to arXiv v3 identify the earlier published version.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem dual_convex_and_attains_minimum {n : ℕ} (M : Instance n)
    (B : ℝ) (hslater : ∃ i : Box n, M.cost i < B) :
    (∀ x y a : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ a → a ≤ 1 →
      dualValue M B (a * x + (1 - a) * y) ≤
        a * dualValue M B x + (1 - a) * dualValue M B y) ∧
    ∃ multiplier : ℝ, dualMinimizer M B multiplier := by sorry

end PandoraBO.Private20261023
