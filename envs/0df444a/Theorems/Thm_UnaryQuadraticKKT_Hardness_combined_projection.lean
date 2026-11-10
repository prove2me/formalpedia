-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_combined_projection
-- name    : UnaryQuadraticKKT.Hardness.combined_projection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:46:28.703301+00:00
-- url     : https://prove2.me/theorems/7b8e0a66-7e10-44b9-92fa-3493f54876c5
-- title:
--   Proposition 4.6 — every combined KKT point projects to the normalized KKT set
-- statement:
--   Let $n\ge1$, let $P$ be an arbitrary rational quadratic, and construct $\widetilde P$ and its combined polynomial $G$ from the actual binary digits of its cleared coefficients. For every real point $(x',u')$,
--   $$
--   (x',u')\in\operatorname{KKT}_{[0,1]^n\times\prod_r[-1,1]^{m_r}}(G)
--   \quad\Longrightarrow\quad x'\in\operatorname{KKT}_{[0,1]^n}(\widetilde P).
--   $$
--   The premise includes feasibility on the mixed box and uses its actual coordinate boundaries. No assumption selects an auxiliary minimizer in advance. The statement retains zero inputs, square monomials, linear factors and shared original coordinates. It is the every-point analytic guarantee needed by the computational decoder.
--
--   Differences from the source:
--   - encoding: the monomial convention of Equation (2) → the published objective ½xᵀQx+cᵀx with Q_ii=2q_ii and Q_ij=Q_ji=q_ij for i<j; reason: this invertible rational coefficient conversion preserves the entire polynomial and all its derivatives
--   - encoding: the product [0,1]^n × ∏_r[-1,1]^(k_r+2) → functions on the disjoint sum Fin n ⊕ Σ_r Fin (k_r+2); reason: each dependent pair identifies one auxiliary coordinate; original coordinates are shared, and the empty product is allowed
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Proposition 4.6, p.9. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Combined

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness
open NetworkEquilibriumCLS.LinearNash

/-- Proposition 4.6, p.9. Every real KKT point, with no chosen minimizer hypothesis. -/
theorem combined_projection {n : ℕ} (hn : 0 < n) (p : Quadratic n)
    (z : CombinedIndex p → ℝ)
    (hz : IntervalKKT (mixedLower p) (fun _ => 1) (combinedValue p) z) :
    QuadraticKKT (normalized p) (fun i => z (.inl i)) := by sorry

end UnaryQuadraticKKT.Hardness
