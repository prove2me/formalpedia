-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_weitzman_optimality
-- name    : PandoraBO.Private20261023.weitzman_optimality
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:16.588303+00:00
-- url     : https://prove2.me/theorems/990cec40-a31b-4150-828d-3fa1ecbf32c2
-- title:
--   Theorem 1 — Weitzman cost-per-sample optimality
-- statement:
--   Consider finitely many mutually independent integrable real rewards with strictly positive deterministic opening costs. For every $\lambda>0$, a Gittins policy exists, and every such policy maximizes
--
--   $$R(\pi)-\lambda C(\pi)$$
--
--   over all measurable adaptive randomized policies. The first box must be opened. Afterward the rule selects an unopened maximal-index box and compares its index with the incumbent reward; it may randomize among tied boxes and between stopping and continuing at equality. This is the cost-per-sample result used as a prerequisite to the fixed expected-budget theorem.
-- source:
--   Xie, Astudillo, Frazier, Scully and Terenin, Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index, NeurIPS 2024; arXiv:2406.20062v3 (16 January 2025), https://arxiv.org/pdf/2406.20062v3, Section 3.2, p. 5, Theorem 1 (attributed to Weitzman), applied to the positive scaled costs λc. Mission source version: the author-revised manuscript reviewed on 23 October 2026, intended for arXiv v4; public posting is pending. References to arXiv v3 identify the earlier published version.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem weitzman_optimality {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) :
    (∃ π : Policy n, isGittinsPolicy M multiplier π) ∧
    ∀ π : Policy n, isGittinsPolicy M multiplier π → optimal M multiplier π := by sorry

end PandoraBO.Private20261023
