-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_affine_equivalence
-- name    : UnaryQuadraticKKT.Hardness.affine_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:46:31.168788+00:00
-- url     : https://prove2.me/theorems/2ffe5ea5-9a15-4bc8-961a-a02cc77ee5eb
-- title:
--   Section 4.4, Equation (19) — both directions of the affine box-KKT equivalence
-- statement:
--   Let $n\ge1$, let $P$ be an arbitrary rational quadratic, let $G$ be its computed combined chain, and let $H(x,v)=G(x,2v-1)$. For every real vector $(x,v)$,
--   $$
--   (x,v)\in\operatorname{KKT}_{[0,1]^{n+M_{\rm aux}}}(H)
--   \quad\Longleftrightarrow\quad
--   (x,2v-1)\in\operatorname{KKT}_{[0,1]^n\times\prod_r[-1,1]^{m_r}}(G).
--   $$
--   Both sides include feasibility and every endpoint condition. The constant term in $H$ is retained. The equivalence transfers the full KKT relation when the auxiliary variables are moved onto the unit interval.
--
--   Differences from the source:
--   - encoding: the product [0,1]^n × ∏_r[-1,1]^(k_r+2) → functions on the disjoint sum Fin n ⊕ Σ_r Fin (k_r+2); reason: each dependent pair identifies one auxiliary coordinate; original coordinates are shared, and the empty product is allowed
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Section 4.4, Equation (19), p.10. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Combined

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness
open NetworkEquilibriumCLS.LinearNash

/-- Section 4.4, Eq. (19), p.10; feasibility and all boundary signs occur on both sides. -/
theorem affine_equivalence {n : ℕ} (hn : 0 < n) (p : Quadratic n)
    (z : CombinedIndex p → ℝ) :
    FunctionKKT (affineValue p) z ↔
      IntervalKKT (mixedLower p) (fun _ => 1) (combinedValue p) (affinePoint p z) := by sorry

end UnaryQuadraticKKT.Hardness
